FROM coqorg/coq:8.11.2-ocaml-4.11.2-flambda

MAINTAINER Vasily Pestun "pestun@ihes.fr"

RUN sudo apt-get update && \
    sudo apt-get --yes install graphviz pkg-config libev-dev libxxhash-dev \
    cmake build-essential capnproto libcapnp-dev python3 python3-venv python3-dev

COPY --chown=coq:coq . coq-tactician-api

WORKDIR coq-tactician-api

RUN eval $(opam env) && opam update \
    && opam install -t ./coq-tactician-api.opam -y

RUN python3 -m venv ./venv && ./venv/bin/pip install .

# run script proof as in former pytact-test
RUN opam exec -- ./venv/bin/pytact-prover --with-coq --loglevel=INFO

# run script proof over a single tcp connection

RUN opam exec -- ./venv/bin/pytact-prover --tcp --with-coq --tcp-sessions 1  --loglevel=INFO

# run dfs proof on a sample file prop with 4 variables in a single tcp session

RUN opam exec -- ./venv/bin/pytact-prover  --tcp --with-coq --tcp-sessions 1 --dfs --test prop4.txt --loglevel=ERROR --dfs-limit=20