(** * The chromatic bound for K_t-minor-free hypergraphs implies their 3-colourability for t = 3

At t = 3 the bound ⌈3(t-1)/2⌉ is 3, so the first half of Steiner's Conjecture 2 (every hypergraph
without K_t minor has a proper colouring with ⌈3(t-1)/2⌉ colours) is exactly his Problem 1.

The implication is the edge e049 of relations.json in graph-conjectures.  It was formalized in
graph-theory-rocq (hypergraph-theory/theories/conjectures/implications_X225.v). *)

From mathcomp Require Import boot.
From GC.hypergraph.AX_kt_minor_free_hypergraph_chromatic_bound Require Import
  main(AX_kt_minor_free_hypergraph_chromatic_bound).
From GC.hypergraph.AX_kt_minor_free_hypergraph_3_colorable Require Import
  main(AX_kt_minor_free_hypergraph_3_colorable).

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Theorem AX_kt_minor_free_hypergraph_chromatic_bound_implies_AX_kt_minor_free_hypergraph_3_colorable
  : AX_kt_minor_free_hypergraph_chromatic_bound -> AX_kt_minor_free_hypergraph_3_colorable.
Proof. by move=> H T E; case: (H 3 isT) => /(_ T E). Qed.

Check
  (AX_kt_minor_free_hypergraph_chromatic_bound_implies_AX_kt_minor_free_hypergraph_3_colorable :
GC.hypergraph.AX_kt_minor_free_hypergraph_chromatic_bound.main.AX_kt_minor_free_hypergraph_chromatic_bound
  ->
GC.hypergraph.AX_kt_minor_free_hypergraph_3_colorable.main.AX_kt_minor_free_hypergraph_3_colorable).
Print Assumptions
  AX_kt_minor_free_hypergraph_chromatic_bound_implies_AX_kt_minor_free_hypergraph_3_colorable.
