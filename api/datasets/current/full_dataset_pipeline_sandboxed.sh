#!/bin/bash

sudo docker build -t coq-tactician-api-dataset -f datasets/current/Dockerfile .
mkdir output
sudo docker run -v $(pwd)/output:/home/dataset-maker/output/ \
       -it --privileged coq-tactician-api-dataset -c '
           ./coq-tactician-api/datasets/current/stage1.sh &&
           ./coq-tactician-api/datasets/current/stage2.sh &&
           ./coq-tactician-api/datasets/current/stage3.sh &&
           eval $(opam env --root=./opam-root --set-root) &&
           . ./venv/bin/activate
           ./coq-tactician-api/datasets/current/make_dataset.sh ./output/v15-opam-coq8.11-partial
           '
