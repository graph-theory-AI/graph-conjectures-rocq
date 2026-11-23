# Rocq formalization of some proofs in graph theory

This file is mostly written by humans. AI corrections must be approved by humans and remain concise.

## Overall description

This repository is a companion to [graph-conjectures](https://github.com/graph-theory-AI/graph-conjectures), which lists around one thousand conjectures in graph theory. It is intended to be a reorganized version of [graph-theory-rocq](https://github.com/graph-theory-AI/graph-theory-rocq). It contains the following, formalized in [Rocq](https://rocq-prover.org/):

- conjecture statements,
- proofs or disproofs of some conjectures,
- proofs of some relations between conjectures,
- a tentative library for graph proofs.

Each of these has a dedicated directory in `theories/`. Conjectures are grouped by topic: chromatic, digraph, extremal, hamiltonicity, hypergraph, etc., and misc for those that do not fit an identified topic. Most of the work is done by prompting LLMs (mainly Claude and ChatGPT) and is still in progress.

We rely on the following Rocq libraries:

- [MathComp](https://math-comp.github.io/)
- [GraphTheory](https://github.com/rocq-community/graph-theory)

### Statements

Each conjecture statement is written in a single `conj-name.v` Rocq file where `conj-name` is the canonical name of the conjecture (according to `graph-conjectures/data/conjecture_names.json`). It contains all necessary definitions that are not in MathComp or GraphTheory. An opening comment presents the non-standard definitions and the conjecture statement in English. A comment separates the definitions of the local graph library from those more specific to the conjecture.

### Conjecture proofs

Some of the proofs come from [Graph-Theory-LLM-Proofs](https://github.com/graph-theory-AI/Graph-Theory-LLM-Proofs). Some of them were simplified through user prompting. For each conjecture, we have a `conj-name/` directory containing a `main.v` file that presents the statement and imports the proof, which is itself contained in one or more files (possibly organized in subdirectories). 

### Checking a proof

To check a proof, it suffices to read `main.v` and run Rocq on it. This file is minimal: it contains a module `Spec` with a copy of `conj-name.v` (including the necessary definitions beyond those of MathComp and GraphTheory) and a proposition named, e.g., `Target`, that states the conjecture. It then imports the files of the proof and states a theorem of the form `Theorem conj_holds : Spec.Target.` with a one-line proof by an imported lemma. The final `Print Assumptions conj_holds.` command should produce the message `Closed under the global context`.

### Relation proofs

Each proof $A \Rightarrow B$ (or $A \Leftrightarrow B$) is contained in a directory `A--B/`, where `A` and `B` are the canonical names of conjectures $A$ and $B$, respectively. The directory has the same structure as for conjecture proofs, and the proof can be checked similarly.

### Graph library

A definition, lemma or theorem is added to the library if it is considered standard in the literature or if it is used in at least two proofs concerning distinct conjectures or relations.



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
