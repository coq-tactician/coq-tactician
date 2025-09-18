eval $(opam env --root=./opam-root --set-root)
time opam install --yes --keep-build-dir coq-tactician-stdlib.8.11.dev
opam switch export opam-stage2 --freeze
