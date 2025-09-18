"""Find all axioms in the dataset (used to find false hypotheses in packages)
"""

from pathlib import Path
import sys
from pytact.data_reader import data_reader, Original, ManualSectionConstant
import pytact.graph_api_capnp_cython as apic

def main():
    dataset_path = Path(sys.argv[1]).resolve()
    with data_reader(dataset_path) as data:
        for f in data.values():
            for d in f.definitions():
                if not isinstance(d.status, Original):
                    continue
                if isinstance(d.kind, ManualSectionConstant):
                    continue
                if apic.EdgeClassification(d.node.children[0][0]).name == 'CONST_UNDEF':
                    print(d.kind)
                    print(d.name)
                    print(d.type_text)
                    print(d.term_text)

if __name__ == "__main__":
    exit(main())
