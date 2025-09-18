"""Calculate the size of proofs, propositions, functions and other things."""

from pathlib import Path
import statistics
import sys
from pytact.data_reader import data_reader, Original, Node, Constructor, Inductive, Projection
import pytact.graph_api_capnp as api

def size(n : Node):
  seen = set()
  count = 0
  def rec(n : Node):
      nonlocal count
      nonlocal seen

      if n in seen:
          return # Shared node in the DAG, was already counted
      if n.label.is_definition or n.label.is_evar:
        return # When we reach a definition or evar, we assume we can look it up; stop counting
      count += 1
      seen.add(n)
      if n.label.is_rel:
          return # Prevent infinite recursion from variable nodes
      for _, c in n.children:
          rec(c)
  
  rec(n)
  return count

def summary(arr):
    return f"count {len(arr)}; min {min(arr)}; max {max(arr)}; median {statistics.median(arr)}; mean {statistics.mean(arr)}"

def main():

    stats = { 
        "proofs" : [],
        "propositions" : [],
        "function_body" : [],
        "function_type" : [],
        "goals" : [],
    }

    sys.setrecursionlimit(150000)
    dataset_path = Path(sys.argv[1]).resolve()
    with data_reader(dataset_path) as data:
        for f in data.values():
            #if f.filename != Path("coq-tactician-stdlib.8.11.dev/theories/Init/Logic.bin"):
            #    continue
            print(f.filename)
            for d in f.definitions(across_files=False, spine_only=False):
                if not isinstance(d.status, Original):
                    continue # Only consider original objects that the AI is likely to need to generate. No derived objects through section or module substitution.
                if isinstance(d.kind, (Inductive, Constructor, Projection)):
                    continue # Too lazy to count the size of inductive definitions for now
                assert (len(d.node.children) == 2)
                if d.node.children[0][0] == api.EdgeClassification.constOpaqueDef:
                    stats["proofs"].append(size(d.node.children[0][1]))
                    stats["propositions"].append(size(d.node.children[1][1]))
                elif d.node.children[0][0] == api.EdgeClassification.constDef:
                    stats["function_body"].append(size(d.node.children[0][1]))
                    stats["function_type"].append(size(d.node.children[1][1]))
                    #print(f"{d.name}\t{size(d.node.children[1][1])}")

                if proof := d.proof:
                    for stepi, step in enumerate(proof):
                        for oi, outcome in enumerate(step.outcomes):
                            #print(f"{d.name} step {stepi} outcome {oi} : {size(outcome.before.root)}")
                            stats["goals"].append(size(outcome.before.root))

    for k,v in stats.items():
        print(f"{k} : {summary(v)}")
                

if __name__ == "__main__":
    exit(main())
