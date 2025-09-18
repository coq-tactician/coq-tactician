if [ $# -lt 1 ]
then
    echo "Usage: ./gen-pdoc.sh output-dir"
    exit 1
fi

OUTPUTDIR=${1}; shift

rm pytact/data_reader.cpython*
cp pytact/data_reader.pyi pytact/data_reader.py

pdoc --logo https://coq-tactician.github.io/images/logo.png \
     --logo-link http://coq-tactician.github.io \
     --footer-text PyTactician \
     --edit-url pytact=https://github.com/coq-tactician/coq-tactician-api/tree/coq8.11/pytact/ \
     --docformat markdown \
     --output-directory "$OUTPUTDIR" \
     pytact \!pytact.generate_api

rm pytact/data_reader.py
