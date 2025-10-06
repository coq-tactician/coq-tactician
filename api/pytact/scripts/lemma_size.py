"""Calculate the number of proof state refinements in each lemmas proof."""

from pathlib import Path
import sys
from pytact.data_reader import data_reader, Original

def main():
    dataset_path = Path(sys.argv[1]).resolve()
    with data_reader(dataset_path) as data:
        for f in data.values():
            for d in f.definitions():
                if not isinstance(d.status, Original):
                    continue
                if proof := d.proof:
                    count = 0
                    for step in proof:
                        for outcome in step.outcomes:
                            count += 1
                    print(f"{d.name}\t{count}")

if __name__ == "__main__":
    exit(main())
