(** * Dense bipartite induced subgraphs: from triangle-free graphs to graphs of large girth

Let c be the constant of the triangle-free conjecture (degree at least (log d) / c).  Take
g0 = 4 and d0 = 2 ^ (3c): a graph of girth at least 4 is triangle-free, hence it has a nonempty
bipartite induced subgraph in which every degree is at least (log d0) / c = 3.

The implication is the edge e063 of relations.json in graph-conjectures.  It was formalized in
graph-theory-rocq (extremal-graph-theory/theories/conjectures/implications_X13.v). *)

From GraphTheory Require Import digraph sgraph.
From mathcomp Require Import boot.
From GC.extremal.AX_dense_bipartite_induced_triangle_free_log Require Import
  main(AX_dense_bipartite_induced_triangle_free_log).
From GC.extremal.AX_dense_bipartite_induced_large_girth Require Import
  main(AX_dense_bipartite_induced_large_girth).
From GC.GraphLib Require Import cycle(girth_ge4_triangle_free).

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Theorem AX_dense_bipartite_induced_triangle_free_log_implies_AX_dense_bipartite_induced_large_girth :
  AX_dense_bipartite_induced_triangle_free_log -> AX_dense_bipartite_induced_large_girth.
Proof.
move=> [c [c0 H]]; exists (2 ^ (3 * c)), 4 => G G0 g4 deg.
have [S [S0 bip degS]] := H _ G G0 (girth_ge4_triangle_free g4) deg.
by exists S; split=> // v; have := degS v; rewrite trunc_expnK // mulnC leq_pmul2l.
Qed.

Check (AX_dense_bipartite_induced_triangle_free_log_implies_AX_dense_bipartite_induced_large_girth :
  GC.extremal.AX_dense_bipartite_induced_triangle_free_log.main.AX_dense_bipartite_induced_triangle_free_log ->
  GC.extremal.AX_dense_bipartite_induced_large_girth.main.AX_dense_bipartite_induced_large_girth).
Print Assumptions AX_dense_bipartite_induced_triangle_free_log_implies_AX_dense_bipartite_induced_large_girth.
