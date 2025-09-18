"""Find all lemmas that depend on ssreflect (approximation)"""

from pathlib import Path
import sys
from pytact.data_reader import data_reader, Original
from pytact.graph_visualize_browse import transitive_closure

ssr_classification = {
    "coq-bits.1.1.0": True,
    "coq-qcert.2.2.0": False,
    "coq-ceres.0.4.0": False,
    "coq-corn.8.16.0": False,
    "coq-bytestring.0.9.0": False,
    "coq-hammer.1.3.2+8.11": False,
    "coq-gaia-stern.1.15": True,
    "coq-mathcomp-apery.1.0.1": True,
    "coq-tlc.20200328": False,
    "coq-iris-heap-lang.3.4.0": True,
    "coq-printf.2.0.0": False,
    "coq-smtcoq.2.0+8.11": False,
    "coq-topology.10.0.1": False,
    "coq-haskell.1.0.0": False,
    "coq-bbv.1.3": False,
    "coq-poltac.0.8.11": False,
    "coq-mathcomp-odd-order.1.14.0": True,
    "coq-hott.8.11": False,
}

def main():
    ssr_lemmas = set()
    normal_lemmas = set()
    dataset_path = Path(sys.argv[1]).resolve()
    with data_reader(dataset_path) as data:
        trans_deps = transitive_closure({d.filename: list(d.dependencies)
                                            for d in data.values()})
        ssr = Path('coq-tactician-stdlib.8.11.dev/plugins/ssr/ssreflect.bin')
        ssr_dependees = [ d for d in data.keys() if ssr in trans_deps[d]]
        for f in data.keys():
            if f.parts[0] in ssr_classification:
                if (f in ssr_dependees) != ssr_classification[f.parts[0]]:
                    print(f)
            # for d in data[f].definitions():
            #     if not isinstance(d.status, Original):
            #         continue
            #     if proof := d.proof:
            #         if f in ssr_dependees:
            #             ssr_lemmas.add(d.name)
            #         else:
            #             normal_lemmas.add(d.name)

    # for l in ssr_lemmas:
    #     print(l)
    for l in normal_lemmas:
        print(l)

if __name__ == "__main__":
    exit(main())
