"""Script used to analyze which proofs the oracle was unable to reproduce and
why."""

from pathlib import Path
import sys
from pytact.data_reader import data_reader, Original

def main():
    benchfile = sys.argv[2]
    unsolved_bench = set()
    with open(benchfile, 'r') as f:
        for line in f.readlines():
            spl = line.split('\t')
            if len(spl) <= 3:
                unsolved_bench.add(spl[1])

    dataset_path = Path(sys.argv[1]).resolve()
    with data_reader(dataset_path) as data:
        for datafile in data.values():
            if datafile.filename.parts[0] != 'coq-tactician-stdlib.dev':
                continue
            for d in datafile.definitions():
                if not isinstance(d.status, Original):
                    continue
                if not d.name in unsolved_bench:
                    continue
                if proof := d.proof:

                    unknown = False
                    for step in proof:
                        if step.tactic is None:
                            unknown = True
                    if unknown:
                        continue

                    arg_unknown = False
                    for step in proof:
                        for outcome in step.outcomes:
                            for arg in outcome.tactic_arguments:
                                if arg is None:
                                    arg_unknown = True
                    if arg_unknown:
                        continue

                    term = False
                    for step in proof:
                        if step.tactic.text != step.tactic.interm_text:
                            term = True
                    if term:
                        continue

                    tactics = { step.tactic.ident for step in proof }
                    for ancestor in d.global_context():
                        if a_proof := ancestor.proof:
                            for step in a_proof:
                                if step.tactic is not None:
                                    tactics.discard(step.tactic.ident)
                    if tactics:
                        continue

                    count = 0
                    for step in proof:
                        for outcome in step.outcomes:
                            count += 1
                    print(f"{count}\t{d.name}")

if __name__ == "__main__":
    exit(main())
