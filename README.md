# The Tactician
## A Seamless, Interactive Tactic Learner and Prover for Coq

![Tactician landing image](assets/landing.png)
Tactician is a tactic learner and prover for the Coq Proof Assistant. The system will help
users make tactical proof decisions while they retain control over the general proof strategy.
To this end, Tactician will learn from previously written tactic scripts, and either gives
the user suggestions about the next tactic to be executed or altogether takes over the burden
of proof synthesis. Tactician’s goal is to provide the user with a seamless, interactive, and
intuitive experience together with strong, adaptive proof automation.

## Installation and Usage

For installation and usage instructions, see the [manual](https://coq-tactician.github.io/manual/).

## Contributing

Tactician welcomes contributions of any kind. To get started hacking on Tactician, you first
need to learn how to build it manually. These instructions assume basic understanding
of Coq, OCaml, Opam and Dune. If not, it is recommended that you first go through the
[manual](https://coq-tactician.github.io/manual/) before contributing.
1. Make sure that you have an Opam switch available and that you have this repository checked out.
2. Add the required Coq repositories to your Opam switch:
   ```
   opam repo add coq-released https://coq.inria.fr/opam/released
   opam repo add coq-core-dev https://coq.inria.fr/opam/core-dev
   opam repo add coq-extra-dev https://coq.inria.fr/opam/extra-dev
   ```
   Optionally, but recommended, add a custom repository for Tactician that includes a version
   of Coq with some bug-fixes that have been back-ported to older versions:
   ```
   opam repo add custom-archive https://github.com/LasseBlaauwbroek/custom-archive.git
   ```
3. Ensure that you have the proper dependencies installed by running
   `opam install . --deps-only --with-test`.
4. You can now build Tactician using `dune build`.
5. Due to limitations in Dune, Tactician currently cannot be executed or used without being
   installed first (in particular `dune exec ..` does not work). If you want to test your
   changes, you have two options:
   - **Slow but safe:** Pin and install your local changes to Tactician with `opam install . -w`.
     This approach is slow because Opam has a lot of overhead due to dependency-solving.
   - **Fast but unsafe:** After running `dune build` let Dune take care of the installation by
     running `dune install`. This option is unsafe, because it bypasses Opam. This means that
     no dependency-solving is performed, and Opam will not know how to remove Tactician (it
     will not even know it was installed).
     
   The best of both worlds may be to install Tactician through Opam once so that it at least
   knows that _some_ version of Tactician is installed, and then update quickly using `dune install`.

## Git Branching Model

Tactician is a plugin for Coq that supports all versions between Coq 8.10 and master. We do this
in order to maximize the number of Coq developments with which we can benchmark.

Because Coq does not guarantee backwards compatibility of its plugin API, we have to maintain different
versions of Tactician for every major Coq version. Hence, we haven an active branch for every
supported Coq version called `coq8.10`, `coq8.11`, `coq8.12`, ..., `coqdev`. The main development
of Tactician is done in one of these branches, currently `coq8.11`. Once in a while (whenever
is convenient), all the changes in `coq8.11` are merged into the other branches and any tweaks
needed for Coq's ever-changing API are applied. This propagation works as follows:
```
                                                                      incoming change
                                                                             |
                                                                       merge |
                                                                             |
    merge      merge      merge      merge      merge      merge      merge  ⯆   merge
dev <---- 8.16 <---- 8.16 <---- 8.15 <---- 8.14 <---- 8.13 <---- 8.12 <---- 8.11 ----> 8.10
```
Changes that target a branch other than the default branch are only allowed to fix a problem
that manifests itself in specific versions of Coq.

Whenever a new Coq release candidate `8.xx` gets branched off upstream, a new branch `coq8.xx`
will also be branched off from `coqdev` in Tactician.

Tactician is currently not yet part of the test-suite of Coq, meaning that we don't get overlays
when an API is changed upstream. Instead, a daily CI test is run to compile Tactician against
the latest upstream `master` branch.

In order to ensure some stability to develop Tactician, it's default branch does not move
every time a new Coq version is released. However, we may still move the default branch once
in a while to benefit from upstream changes that increase developer comfort.
