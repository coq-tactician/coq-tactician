import argparse
from multiprocessing import Pool
from pathlib import Path
from functools import partial
from collections import Counter
import math
from pytact.data_reader import GlobalContextSets, lowlevel_data_reader, lowlevel_to_highlevel, Definition, Node, Original, Substituted, Discharged, node_dependencies, definition_dependencies
import pytact.graph_api_capnp_cython as apic
import capnp
import pytact.graph_api_capnp as graph_api_capnp

def open_dataset(dataset_path: Path):
    global ctx
    ctx = lowlevel_data_reader(dataset_path)
    global data
    data = ctx.__enter__()
    global node_counts
    node_counts = [len(data[i].graph.nodes) for i in range(0, len(data.graph_files))]
    global hdata
    hdata = lowlevel_to_highlevel(data)
    global global_contexts
    global_contexts = GlobalContextSets.new_context().__enter__()

# def node_dependencies(n: Node, deps: set[Definition] | None = None) -> set[Definition]:
#     if deps is None:
#         deps = set()
#     seen: set[Node] = set()
#     stack = [n]
#     while stack:
#         node = stack.pop()
#         if node in seen:
#             continue
#         seen.add(node)
#         if d := node.definition:
#             deps.add(d)
#             continue
#         for _, child in node.children:
#             stack.append(child)
#     return deps

# def definition_dependencies(d: Definition):
#     deps = set()
#     for _, c in d.node.children:
#         node_dependencies(c, deps)
#     return deps

def process1(args, fname: Path):
    file_errors = []
    file_definitions = 0
    file_original_definitions = 0
    file_base_tactics_text = set()
    file_base_tactics_intermtext = set()
    file_tactics = Counter()
    file_original_tactics = Counter()
    file_tactic_arguments = {}
    file_tactic_ident_to_base = {}
    proof_steps = 0
    original_proof_steps = 0
    original_proof_steps_faithful = 0
    outcomes = 0
    original_outcomes = 0
    proofs = 0
    original_proofs = 0
    original_proofs_faithful = 0
    unresolvable = 0
    file_disappearing_proof_states = 0
    graphid = data.graphid_by_filename[fname]
    freader = data[graphid]
    graph = freader.graph
    nodes_count = node_counts[graphid]
    edges_count = len(graph.edges)
    dependency_count = len(freader.dependencies)
    print(f"Checking file {fname}: {nodes_count} nodes and {edges_count} edges")

    # Check correctness of Graph struct
    for n in graph.nodes:
        if not (n.children_index + n.children_count <= edges_count):
            file_errors.append(f"{fname}: Children of node {n} are not valid indices of Graph.edges")
        if n.label.is_definition:
            file_definitions += 1

    for t in graph.edges:
        target = t.target
        dep_index = target.dep_index
        if dep_index >= dependency_count:
            file_errors.append(f"{fname}: target.depIndex {t.target.dep_index} "
                  f"but len(g.dependencies) is {dependency_count} "
                  f"and g.dependencies = {freader.dependencies}")
        if target.node_index >= node_counts[data.local_to_global(graphid, dep_index)]:
            file_errors.append(f"{fname}: Reference for target {t} is out of bounds")

    # Check correctness of Dataset struct
    if file_definitions != len(freader.definitions):
        file_errors.append(f"{fname}: Counted {file_definitions} definitions in the file, "
                        f"but Dataset.definitions has size {len(freader.definitions)}")

    hreader = hdata[fname]
    with global_contexts.sub_context(lambda d: d.is_file_representative) as sub_global_contexts:
        for d in hreader.definitions():
            if not d.node.definition:
                file_errors.append(f"{fname}: Node {d.node} should be a definition but is not")

            # Check correctness of Definition struct
            if isinstance(d.status, Original):
                file_original_definitions += 1
            elif isinstance(d.status, Discharged):
                if not d.status.original.node.definition:
                    file_errors.append(f"{fname}: Discharged node of definition {d.name} "
                                       f"is not a definition")
            elif isinstance(d.status, Substituted):
                if not d.status.original.node.definition:
                    file_errors.append(f"{fname}: Substituted node of definition {d.name} "
                                       f"is not a definition")

            def check_in_global_context(s):
                global_context = sub_global_contexts.global_context_set(d)
                for dd in s:
                    if dd not in global_context:
                        file_errors.append(f"{fname}: Definition {d.name} has dependency {dd.name} "
                                        f"which is not part of its global context")

            if not args.quick:
                check_in_global_context(definition_dependencies(d))

            crepr = d.cluster_representative
            if d not in d.cluster:
                file_errors.append(f"{fname}: Cluster represented by {crepr.name}"
                                f"does not contain {d.name}")
            for cd in d.cluster:
                if crepr != cd.cluster_representative:
                    file_errors.append(f"{fname}: Cluster represented by {crepr.name} contains unrelated "
                                    f"definition {cd.name}")
            if prev := d.previous:
                if not prev.node.definition:
                    file_errors.append(f"{fname}: Previous node of definition {d.name} is not a definition")
            for ep in d.external_previous:
                if not ep.node.definition:
                    file_errors.append(f"{fname}: External dependency of definition {d.name} is "
                                    f"not a definition")
            if ps := d.proof:
                proofs += 1
                faithful = True
                before_states = set()
                for p in ps:
                    for outcome in p.outcomes:
                        before_states.add(outcome.before.id)
                for p in ps:
                    proof_steps += 1
                    if t := p.tactic:
                        ident = t.ident
                        file_base_tactics_text.add(t.base_text)
                        file_base_tactics_intermtext.add(t.interm_text)
                    else:
                        ident = 0
                    file_tactics[ident] += 1
                    if isinstance(d.status, Original):
                        file_original_tactics[ident] += 1
                        original_proof_steps += 1
                        if (t := p.tactic) and t.text == t.interm_text:
                                original_proof_steps_faithful += 1
                        else:
                            faithful = False
                    for outcome in p.outcomes:
                        for after in outcome.after:
                            if after.id not in before_states:
                                file_disappearing_proof_states += 1

                        if not args.quick:
                            check_in_global_context(node_dependencies(outcome.term))
                        for state in [outcome.before] + list(outcome.after):
                            root_label = state.root.label
                            if not root_label.is_proof_state:
                                file_errors.append(f"{fname}: root is proof state {state} is {root_label}")

                            if not args.quick:
                                check_in_global_context(node_dependencies(state.root))
                            if len(state.context) != len(state.context_names):
                                file_errors.append(f"{fname}: Length of context is different from length of"
                                                f"context_names in proof state {state}")
                            if len(state.context) != len(state.context_text):
                                file_errors.append(f"{fname}: Length of context is different from length of"
                                                f"context_text in proof state {state}")
                            root_children = [child for _, child in state.root.children]
                            for c in state.context:
                                if c not in root_children:
                                    file_errors.append(
                                        f"{fname}: hyp {c} of state {state} in def {d.name} is not "
                                        f"reachable from the root")
                                if not (c.label.is_context_def or c.label.is_context_assum):
                                    file_errors.append(
                                        f"{fname}: ctx {state.context} of a state {state} "
                                        f"has the wrong node classification {c.label}")

                        file_tactic_arguments.setdefault(ident, len(outcome.tactic_arguments))
                        if t := p.tactic:
                            file_tactic_ident_to_base.setdefault(ident, t.base_text)
                        if file_tactic_arguments[ident] != len(outcome.tactic_arguments):
                            file_errors.append(f"{fname}: Tactic with two different argument lengths detected. : Original: {file_tactic_arguments[ident]} : {file_tactic_ident_to_base[ident]}. New {len(outcome.tactic_arguments)} : {t.text} : {t.base_text}")
                        outcomes += 1
                        if isinstance(d.status, Original):
                            original_outcomes += 1
                        for a in outcome.tactic_arguments:
                            if not a:
                                unresolvable += 1
                            else:
                                if not args.quick:
                                    check_in_global_context(node_dependencies(a))
                if isinstance(d.status, Original):
                    original_proofs += 1
                    if faithful:
                        original_proofs_faithful += 1
    if freader.representative != len(graph.nodes):
        if not graph.nodes[freader.representative].label.is_definition:
            file_errors.append(f"{fname}: Representative {freader.representative} is not a definition")
    for dep in freader.dependencies:
        if Path(dep) not in data.graphid_by_filename:
            file_errors.append(f"{fname}: Dependency {dep} could not be found")


    return (fname, nodes_count, edges_count,
            file_definitions, file_original_definitions, file_base_tactics_text,
            file_base_tactics_intermtext, file_tactics, file_original_tactics, file_tactic_arguments,
            proof_steps, original_proof_steps, original_proof_steps_faithful,
            outcomes, original_outcomes, proofs, original_proofs,
            original_proofs_faithful, unresolvable, file_errors, file_disappearing_proof_states)

def entropy(d):
    n = sum(d.values())
    return -sum([(c / n) * math.log(c / n, 2) for c in d.values()])

def main2():
    parser = argparse.ArgumentParser(
        description = 'Run sanity checks on a dataset and print some statistics.',
        formatter_class=argparse.ArgumentDefaultsHelpFormatter)

    parser.add_argument('dataset',
                        type=str,
                        help=('The location of the dataset to check. ' +
                              'Either a dataset directory, or a SquashFS image, ' +
                              'which will be automatically mounted.'))
    parser.add_argument('--jobs',
                        type=int,
                        default=None,
                        help='number of parallel multiprocessing jobs to run')
    parser.add_argument('--quick',
                        action='store_true',
                        help='skip the more expensive checks')
    parser.add_argument('--verbose',
                       type = int,
                       default = 0,
                       help='level of being verbose 0,1..')

    args = parser.parse_args()

    import sys
    sys.setrecursionlimit(10000)

    dataset_path = Path(args.dataset).resolve()

    errors = []
    tactics = Counter()
    original_tactics = Counter()
    tactic_arguments = {}
    base_tactics_text = set()
    base_tactics_intermtext = set()
    definitions = 0
    original_definitions = 0
    nodes_total = 0
    edges_total = 0
    proof_steps_total = 0
    original_proof_steps_total = 0
    original_proof_steps_faithful_total = 0
    outcomes_total = 0
    original_outcomes_total = 0
    proofs_total = 0
    original_proofs_total = 0
    original_proofs_faithful_total = 0
    unresolvable_total = 0
    disappearing_proof_states = 0

    with lowlevel_data_reader(dataset_path) as data:
        file_list = data.graph_files

    process1_partial = partial(process1, args)
    with Pool(args.jobs, open_dataset, [dataset_path]) as pool:
        results = pool.map(process1_partial, file_list, chunksize=1)
    # file_list = file_list[280:360]
    # print(file_list)
    # open_dataset(dataset_path)
    # results = [process1(args, f) for f in file_list]

    for res in results:
        (fname, nodes_count, edges_count,
         file_definitions, file_original_definitions, file_base_tactics_text,
         file_base_tactics_intermtext, file_tactics, file_original_tactics, file_tactic_arguments,
         proof_steps, original_proof_steps, original_proof_steps_faithful,
         outcomes, original_outcomes, proofs, original_proofs,
         original_proofs_faithful, unresolvable, file_errors, file_disappearing_proof_states) = res
        nodes_total += nodes_count
        edges_total += edges_count
        proof_steps_total += proof_steps
        original_proof_steps_total += original_proof_steps
        original_proof_steps_faithful_total += original_proof_steps_faithful
        outcomes_total += outcomes
        original_outcomes_total += original_outcomes
        proofs_total += proofs
        original_proofs_total += original_proofs
        original_proofs_faithful_total += original_proofs_faithful
        definitions +=  file_definitions
        original_definitions += file_original_definitions
        base_tactics_text.update(file_base_tactics_text)
        base_tactics_intermtext.update(file_base_tactics_intermtext)
        tactics += file_tactics
        original_tactics += file_original_tactics
        disappearing_proof_states += file_disappearing_proof_states
        errors += file_errors
        for tac, length in file_tactic_arguments.items():
            tactic_arguments.setdefault(tac, length)
            if tactic_arguments[tac] != length:
                errors.append(f'{fname}: Tactic with two different argument lengths detected: {tac}')

        unresolvable_total += unresolvable

    for error in errors:
        print(error)

    print(f"Errors encountered {len(errors)}")
    print(f"Nodes total {nodes_total}")
    print(f"Edges total {edges_total}")
    print(f"Tactics total {len(tactics)}")
    print(f"Original tactics total {len(original_tactics)}")
    print(f"Tactics entropy (bits) {entropy(tactics)}")
    print(f"Original tactics entropy (bits) {entropy(original_tactics)}")
    print(f"Tactics base text total {len(base_tactics_text)}")
    print(f"Tactics base intermtext total {len(base_tactics_intermtext)}")
    print(f"Definitions total {definitions}")
    print(f"Original definitions total {original_definitions}")
    print(f"Proof steps total {proof_steps_total}")
    print(f"Original proof steps total {original_proof_steps_total}")
    print(f"Faithfully represented original proof steps total {original_proof_steps_faithful_total}")
    print(f"Outcomes total {outcomes_total}")
    print(f"Original outcomes total {original_outcomes_total}")
    print(f"Proofs total {proofs_total}")
    print(f"Original proofs total {original_proofs_total}")
    print(f"Faithful original proofs total {original_proofs_faithful_total}")
    print(f"Unresolvable tactic arguments {unresolvable_total}")
    print(f"Disappearing proof states (spooky action at a distance) {disappearing_proof_states}")

    if (args.verbose >= 1):
        print("Tactics base text:")
        for t in base_tactics_text:
            print(t)
        print("Tactics intermtext text:")
        for t in base_tactics_intermtext:
            print(t)

    if len(errors) > 0:
        raise Exception("Errors occurred")

def main():
    # import pstats, cProfile
    # cProfile.runctx("main2()", globals(), locals(), "Profile.prof")
    # s = pstats.Stats("Profile.prof")
    # s.strip_dirs().sort_stats("time").print_stats()
    main2()

if __name__ == '__main__':
    main()
