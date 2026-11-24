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

Each conjecture has a directory `theories/topic/conj_name/`, where `conj_name` is the canonical name of the conjecture (according to `graph-conjectures/data/conjecture_names.json`). It is formalized in the Rocq file `main.v`. An opening comment presents the non-standard definitions and the conjecture statement in English. Then come all necessary definitions that are not in MathComp or GraphTheory, with a comment separating those of the local graph library (which are copied to make the file self-contained) from those more specific to the conjecture. Finally, a proposition named `statement` states the conjecture, or its negation if the conjecture is believed to be false. A comment before it indicates which one it is.

### Conjecture proofs

Some of the proofs come from [Graph-Theory-LLM-Proofs](https://github.com/graph-theory-AI/Graph-Theory-LLM-Proofs). Some of them were simplified through user prompting. If `statement` is proved, the proof is contained in one or more additional files (possibly organized in subdirectories) in the directory of the conjecture. A minimalist `proof.v` states a theorem of the form `Theorem statement_holds : main.statement.` with a one-line proof by a lemma from another file. `proof.v` requires `main` and that file without importing them.

### Checking a proof

A sanity check is included in the form of `Check (statement_holds : full.path.to.main.statement).` and `Print Assumptions statement_holds.`. After Rocq compilation, it suffices to read `main.v`, `proof.v` and the Rocq messages of the latter, and to verify that the full path is the correct one. For a more robust check, `make check C=theories/topic/conj_name` generates appropriate files for [rocq-comparator](https://github.com/LLM4Rocq/rocq-comparator) and runs it.

### Relation proofs

Each proof $A \Rightarrow B$ is contained in a file `A/implies_B.v`, where `A/` is the directory of conjecture $A$ and `B` is the canonical name of Conjecture $B$. It is similar to a `proof.v` with similar checking possibilities. If $A$ is disproved, we omit such proofs.

### Graph library

A definition, lemma or theorem is added to the library if it is considered standard in the literature or if it is used in at least two proofs concerning distinct conjectures or relations. It must have no equivalent in MathComp or GraphTheory. 



## Progress

Progress is reported (mostly by AI agents) in:

- [statements.md](progress/statements.md) (TODO-nb statements formalized)
- [conjecture-proofs.md](progress/conjecture-proofs.md) (TODO-nb conjectures proved or disproved)
- [relation-proofs.md](progress/relation-proofs.md) (TODO-nb relations proved)
- [graph-library.md](progress/graph-library.md) (TODO-nb definitions and TODO-nb statements)


## Installation

To check the proofs, you need Rocq 9.2 plus some libraries that can be installed through [opam](https://opam.ocaml.org/):
```
TODO
```

Contributors to this repository should have a local copy of [graph-conjectures](https://github.com/graph-theory-AI/graph-conjectures) in `../graph-conjectures` and a local copy of [Graph-Theory-LLM-Proofs](https://github.com/graph-theory-AI/Graph-Theory-LLM-Proofs) in `../Graph-Theory-LLM-Proofs` to ease the work. (Run your favorite agent from `..`.) Begin by asking the agent to follow the guidelines in this file.


## Directives for AI agents

- AI agents can read this file. They can polish the English, correct inconsistencies or add missing points if the user approves the change.
- Writing new files or creating new directories other than those described above requires user approval.
- All approvals mentioned here are mandatory, even in auto mode.
- Before working on any proof, read the summaries in `references/` and the statements in `theories/GraphLib`. Proofs mostly use SSReflect (the small-scale reflection technique).


## License

This repository is distributed under the [Apache License 2.0](LICENSE); see [NOTICE.md](NOTICE.md) for copyright and third-party material.
