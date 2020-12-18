(lang dune 2.5)
(name coq-tactician)
(using coq 0.2)

(generate_opam_files true)

(source (github coq-tactician/coq-tactician))
(homepage "https://coq-tactician.github.io")
(authors "Lasse Blaauwbroek <lasse@blaauwbroek.eu>")
(maintainers "Lasse Blaauwbroek <lasse@blaauwbroek.eu>")

(package
  (name coq-tactician)
  (synopsis "Tactician: A Seamless, Interactive Tactic Learner and Prover for Coq")
  (description "Tactician is a tactic learner and prover for the Coq Proof Assistant.
The system will help users make tactical proof decisions while they retain
control over the general proof strategy. To this end, Tactician will learn
from previously written tactic scripts, and either gives the user suggestions
about the next tactic to be executed or altogether takes over the burden of
proof synthesis. Tactician's goal is to provide the user with a seamless,
interactive, and intuitive experience together with strong, adaptive proof
automation.")
  (depends
    (ocaml (>= 4.08))
    (dune (and (>= 2.5) :build))
    (opam-client (>= 2.1.0~beta2))
    cmdliner
    (coq (and (>= 8.12) (< 8.13~)))
    conf-git
    (coq-tactician-dummy (and (= 1.0~beta1) :with-test))))