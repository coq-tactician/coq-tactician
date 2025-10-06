"""Print information about all executions of a tactic with a given hash in the dataset."""

from pathlib import Path
import sys
from pytact.data_reader import data_reader

from collections import defaultdict

def main():
    identities = defaultdict(list)

    dataset_path = Path(sys.argv[1]).resolve()
    hid = int(sys.argv[2])
    with data_reader(dataset_path) as data:
        for datafile in data.values():
            for d in datafile.definitions():
                if proof := d.proof:
                    for step in proof:
                        for outcome in step.outcomes:
                            if tac := outcome.tactic:
                                if tac.ident == hid:
                                    print(f"{tac.ident}\n  {datafile.filename}\n  {d.name}\n  "
                                        f"{tac.text}\n  {tac.base_text}\n  {len(outcome.tactic_arguments)} arguments")

if __name__ == "__main__":
    exit(main())
