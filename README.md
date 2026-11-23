# Rocq formalization of some proofs in graph theory

This file is written by humans.

## Overall description

This repository is a companion of [graph-conjectures](https://github.com/graph-theory-AI/graph-conjectures) that lists around one thousand conjectures in graph theory. It contains the formalization in [Rocq](https://rocq-prover.org/) of:

- conjecture statements,
- proofs or disproofs of some conjectures,
- proofs or some relations between conjectures,
- a tentative library for graph proofs.

Each of these has a dedicated directory in `theories/`. Conjectures are grouped by topics: chromatic, digraph, extremal, hamiltonicity, hypergraph,... and misc for the ones remaining out of an identified topic. Most of the work is performed by prompting some LLMs (mainly claude and chatGPT) and is still in progress.

We rely on the following Rocq librairies:

- [MathComp](https://math-comp.github.io/)
- [GraphTheory](https://github.com/rocq-community/graph-theory)

### Statements

Each conjecture statement is written in a single `conj-name.v` Rocq file where `conj-name` is the canonical name of the conjecture (according to `graph-conjectures/data/conjecture_names.json`). It contains all necessary definition which are not in MathComp or GraphTheory. A starting comment presents in english non-standard definitions and the conjecture statement. A comment separates definitions in the  local graph library from those more specific to the conjecture.

### Conjecture proofs

Some of the proofs come from [Graph-Theory-LLM-Proofs](https://github.com/graph-theory-AI/Graph-Theory-LLM-Proofs). Some of them were simplified through user prompting. For each conjecture, we have a `conj-name/` directory containing a `main.v` file presenting the statement and importing the proof which is itself contained in one or more files (possibly organised in sub-directories). 

### Checking a proof

To check the proof, it suffices to read `main.v` besides feeding it to Rocq. `main.v` is minimalist in the sense that it contains a copy of `conj-name.v` (with necessary definitions besides MathComp and GraphTheory) inside a module `Spec` and a statement of the conjecture as `Target`, then imports the files of the proof and state a theorem of the form `Theorem conj_holds : Spec.Target.` whith a one line proof by an imported lemma. The final `Print Assumptions conj_holds.` should produce message `Closed under the global context`.

### Relation proofs

Each proof $A \Rightarrow B$ (or $A \Leftrightarrow B$) is included in a directory `A--B/` where `A`, `B` are the conjecture names of conjectures $A$ and $B$ respectively. The directory has similar structure as for conjecture proofs and can be checked similarly.

### Graph library

A definition, lemma or theorem is added to the library if it is considered as standard in the literature or if it used in at least two proofs concerning distinct conjectures/relations.



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

Constributors of this repository should have a local copy of [graph-conjectures](https://github.com/graph-theory-AI/graph-conjectures) in `../graph-conjectures` and a local copy of [Graph-Theory-LLM-Proofs](https://github.com/graph-theory-AI/Graph-Theory-LLM-Proofs) in `../Graph-Theory-LLM-Proofs` to ease the work. (Run your favorite agent from `..`.) Begin by asking the agent to follow the guidelines in this file.


## Directives for AI agents

- AI agents can read this file, they can polish the english and/or correct some inconsticency or missing point if the correction is approved by the user.
- Writing new files or creating new directories besides what is described above requires user approval.
- All approvals mentioned here are mandatory even in auto mode.
- Before working on any proof, read the summaries in `references/` and the statements in `theories/GraphLib`. Proofs mostly use SSReflect (the small scale reflection formalization technique).
