"""Calculate all lemmas in the testing set whose proofs contain tactics that
were never seen during training."""

from pathlib import Path
import sys
from pytact.data_reader import data_reader, Original

test_packages = set([
    "coq-bits.1.1.0",
    "coq-qcert.2.2.0",
    "coq-ceres.0.4.0",
    "coq-corn.8.16.0",
    "coq-bytestring.0.9.0",
    "coq-hammer.1.3.2+8.11",
    "coq-gaia-stern.1.15",
    "coq-mathcomp-apery.1.0.1",
    "coq-tlc.20200328",
    "coq-iris-heap-lang.3.4.0",
    "coq-printf.2.0.0",
    "coq-smtcoq.2.0+8.11",
    "coq-topology.10.0.1"
    "coq-haskell.1.0.0",
    "coq-bbv.1.3",
    "coq-poltac.0.8.11",
    "coq-mathcomp-odd-order.1.14.0",
    "coq-hott.8.11"
])

def main():
    train_tactics = set()

    dataset_path = Path(sys.argv[1]).resolve()
    with data_reader(dataset_path) as data:
        for f in data.values():
            if f.filename.parts[0] in test_packages:
                continue
            for d in f.definitions():
                if not isinstance(d.status, Original):
                    continue
                if proof := d.proof:
                    for step in proof:
                        if (t := step.tactic) is not None:
                            train_tactics.add(t.ident)

        for f in data.values():
            if f.filename.parts[0] not in test_packages:
                continue
            for d in f.definitions():
                if not isinstance(d.status, Original):
                    continue
                if proof := d.proof:
                    fail = False
                    for step in proof:
                        if step.tactic is not None and step.tactic.ident not in train_tactics:
                            fail = True
                    if not fail:
                        print(d.name)

if __name__ == "__main__":
    exit(main())
