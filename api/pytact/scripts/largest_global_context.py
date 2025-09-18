"""Calculate the definition with the largest global context in a dataset.
"""

from pathlib import Path
import sys
from pytact.data_reader import data_reader, GlobalContextSets

def main():
    dataset_path = Path(sys.argv[1]).resolve()
    maximum = 0
    maxdef = ''
    with data_reader(dataset_path) as data:
        with GlobalContextSets.new_context() as global_contexts:
            for datafile in data.values():
                with global_contexts.sub_context(lambda d: d.is_file_representative) as sub_global_contexts:
                    for d in datafile.definitions():
                        deflen = len(sub_global_contexts.global_context_set(d))
                        if deflen > maximum:
                            maximum = deflen
                            maxdef = d.name
    print(f"{maxdef} : {maximum}")

if __name__ == "__main__":
    exit(main())
