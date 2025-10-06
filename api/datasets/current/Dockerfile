FROM ubuntu:22.04

# Set environment variables to noninteractive for apt
ENV DEBIAN_FRONTEND=noninteractive

# Install system dependencies
RUN apt-get update && apt-get install -y \
    opam \
    graphviz \
    capnproto \
    libcapnp-dev \
    pkg-config \
    libev-dev \
    libxxhash-dev \
    libgmp-dev \
    ruby \
    autoconf \
    libtool \
    squashfs-tools \
    fuse \
    squashfuse \
    python3 \
    python3-venv \
    python3-pip \
    python-is-python3 \
    && rm -rf /var/lib/apt/lists/*

RUN useradd -m dataset-maker
USER dataset-maker
WORKDIR /home/dataset-maker

COPY --chown=dataset-maker:dataset-maker . /home/dataset-maker/coq-tactician-api

RUN python -m venv ./venv && ./venv/bin/pip install ./coq-tactician-api license-expression

ENTRYPOINT ["/bin/bash"]

