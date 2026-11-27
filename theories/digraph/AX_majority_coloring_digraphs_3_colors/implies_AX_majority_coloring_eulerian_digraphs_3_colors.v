(** * Majority 3-colourings of digraphs give those of Eulerian digraphs

The statement for Eulerian digraphs is the statement for all loopless digraphs with the additional
hypothesis that the digraph is Eulerian.

The implication is the edge e017 of relations.json in graph-conjectures.  It was formalized in
graph-theory-rocq (digraph-theory/theories/conjectures/implications_X1.v). *)

From GraphTheory Require Import digraph.
From mathcomp Require Import boot.
From GC.digraph.AX_majority_coloring_digraphs_3_colors Require Import
  main(AX_majority_coloring_digraphs_3_colors).
From GC.digraph.AX_majority_coloring_eulerian_digraphs_3_colors Require Import
  main(AX_majority_coloring_eulerian_digraphs_3_colors).

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Theorem AX_majority_coloring_digraphs_3_colors_implies_AX_majority_coloring_eulerian_digraphs_3_colors :
  AX_majority_coloring_digraphs_3_colors -> AX_majority_coloring_eulerian_digraphs_3_colors.
Proof. by move=> H D irrD _; exact: H. Qed.

Check (AX_majority_coloring_digraphs_3_colors_implies_AX_majority_coloring_eulerian_digraphs_3_colors :
  GC.digraph.AX_majority_coloring_digraphs_3_colors.main.AX_majority_coloring_digraphs_3_colors ->
  GC.digraph.AX_majority_coloring_eulerian_digraphs_3_colors.main.AX_majority_coloring_eulerian_digraphs_3_colors).
Print Assumptions
  AX_majority_coloring_digraphs_3_colors_implies_AX_majority_coloring_eulerian_digraphs_3_colors.
