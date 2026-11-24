# Rocq formalization of some proofs in graph theory

This file is mostly written by humans. AI corrections must be approved by humans and remain concise.

## Overall description

This repository is a companion to [graph-conjectures](https://github.com/graph-theory-AI/graph-conjectures), which lists around one thousand conjectures in graph theory. It is intended to be a reorganized version of [graph-theory-rocq](https://github.com/graph-theory-AI/graph-theory-rocq). It contains the following, formalized in [Rocq](https://rocq-prover.org/):

- conjecture statements,
- proofs or disproofs of some conjectures,
- proofs of some relations between conjectures,
- a tentative library for graph proofs.

Conjectures are grouped by topic: chromatic, digraph, extremal, hamiltonicity, hypergraph, etc., and misc for those that do not fit an identified topic. Each topic has a subdirectory in `theories/`. The library is in `theories/GraphLib/`, with one file per topic. Most of the work is done by prompting LLMs (mainly Claude and ChatGPT) and is still in progress.

We rely on the following Rocq libraries:

- [MathComp](https://math-comp.github.io/)
- [GraphTheory](https://github.com/rocq-community/graph-theory)

### Conjectures

Each conjecture has a directory `theories/topic/conj_name/`, where `conj_name` is the canonical name of the conjecture (according to `graph-conjectures/data/conjecture_names.json`). It is formalized in the Rocq file `main.v`. An opening comment presents the non-standard definitions and the conjecture statement in English. Then come all necessary definitions that are not in MathComp or GraphTheory, with a comment separating those of the local graph library (which are copied to make the file self-contained) from those more specific to the conjecture. Finally, a proposition named `conj_name` states the conjecture.

### Conjecture proofs

Some of the proofs come from [Graph-Theory-LLM-Proofs](https://github.com/graph-theory-AI/Graph-Theory-LLM-Proofs). Some of them were simplified through user prompting. If the conjecture is proved or disproved, the proof is contained in one or more additional files (possibly organized in subdirectories) in the directory of the conjecture. A minimalist `proof.v` states a theorem of the form `Theorem conj_name_holds : conj_name.` or `Theorem conj_name_fails : ~ conj_name.` with a one-line proof by a lemma from another file. `proof.v` imports only the proposition from `main` (`Require Import main(conj_name)`), and requires the other file without importing it.

### Checking a proof

A sanity check is included in the form of `Check (conj_name_holds : full.path.to.main.conj_name).` and `Print Assumptions conj_name_holds.` (or similarly with `conj_name_fails` and `~ full.path.to.main.conj_name`). After Rocq compilation (`make C=theories/topic/conj_name`), it suffices to read `main.v`, `proof.v` and the Rocq messages of the latter, and to verify that the full path is the correct one. For a more robust check, `make check C=theories/topic/conj_name` generates appropriate files for [rocq-comparator](https://github.com/LLM4Rocq/rocq-comparator) and runs it.

### Relation proofs

Each proof $A \Rightarrow B$ is contained in a file `A/implies_B.v`, where `A/` is the directory of conjecture $A$ and `B` is the canonical name of Conjecture $B$. It is similar to a `proof.v`, with a theorem `Theorem A_implies_B : A -> B.` and similar checking possibilities. If $A$ is disproved, we omit such proofs.

### Graph library

A definition, lemma or theorem is added to the library if it is considered standard in the literature or if it is used in at least two proofs concerning distinct conjectures or relations. It must have no equivalent in MathComp or GraphTheory. 



## Progress

Progress is reported (mostly by AI agents) in:

- [conjectures.md](progress/conjectures.md) (1 statements formalized)
- [conjecture-proofs.md](progress/conjecture-proofs.md) (1 conjectures proved or disproved)
- [relation-proofs.md](progress/relation-proofs.md) (0 relations proved)
- [graph-library.md](progress/graph-library.md) (3 definitions and 3 statements)


## Installation

To check the proofs, you need Rocq 9.2 plus some libraries that can be installed through [opam](https://opam.ocaml.org/):
```
opam switch create rocq9.2 ocaml-base-compiler.5.5.1
eval $(opam env --switch=rocq9.2)
opam repo add rocq-released https://rocq-prover.org/opam/released
opam pin add -n rocq-core 9.2.0
opam pin add -n coq-graph-theory "git+https://github.com/rocq-community/graph-theory.git"
opam install rocq-core rocq-mathcomp-ssreflect.2.6.0 rocq-mathcomp-algebra.2.6.0 rocq-mathcomp-fingroup.2.6.0 rocq-mathcomp-zify coq-graph-theory

# optional, for make check
opam pin add rocq-comparator "git+https://github.com/LLM4Rocq/rocq-comparator.git"

# optional, for VSCode (with the VsRocq extension)
opam install vsrocq-language-server

# optional, for rocq-mcp-evolve (claude MCP server for Rocq)
opam pin add --switch=rocq9.2 rocq-mcp-evolve git+https://github.com/LLM4Rocq/rocq-mcp-evolve.git
```

Contributors to this repository should have a local copy of [graph-conjectures](https://github.com/graph-theory-AI/graph-conjectures) in `../graph-conjectures` and a local copy of [Graph-Theory-LLM-Proofs](https://github.com/graph-theory-AI/Graph-Theory-LLM-Proofs) in `../Graph-Theory-LLM-Proofs` to ease the work. (Run your favorite agent from `..`.) Begin by asking the agent to follow the guidelines in this file.


## Directives for AI agents

- AI agents can read this file. They can polish the English, correct inconsistencies or add missing points if the user approves the change.
- Writing new files or creating new directories outside the hierarchy described above requires user approval. In particular, creating a directory and associated files or sub-directories for a conjecture, its topic directory, updating the topic file of the library or `Makefile` or `_CoqProject` or the progress files can be done in auto mode.
- All approvals mentioned here are mandatory, even in auto mode.
- Before working on any proof, read the summaries in `references/` and the statements in `theories/GraphLib`. Proofs mostly use SSReflect (the small-scale reflection technique).


## License

This repository is distributed under the [Apache License 2.0](LICENSE); see [NOTICE.md](NOTICE.md) for copyright and third-party material.
