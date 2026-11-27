(** * Majority 3-colourings of digraphs give those of tournaments

A tournament is a loopless digraph, and the two statements use the same notion of majority
colouring.

The implication is the edge e016 of relations.json in graph-conjectures.  It was formalized in
graph-theory-rocq (digraph-theory/theories/conjectures/implications_X1.v). *)

From GraphTheory Require Import digraph.
From mathcomp Require Import boot.
From GC.digraph.AX_majority_coloring_digraphs_3_colors Require Import
  main(AX_majority_coloring_digraphs_3_colors).
From GC.digraph.AX_majority_coloring_tournaments_3_colors Require Import
  main(AX_majority_coloring_tournaments_3_colors).

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Theorem AX_majority_coloring_digraphs_3_colors_implies_AX_majority_coloring_tournaments_3_colors :
  AX_majority_coloring_digraphs_3_colors -> AX_majority_coloring_tournaments_3_colors.
Proof. by move=> H T [irrT _]; exact: H. Qed.

Check (AX_majority_coloring_digraphs_3_colors_implies_AX_majority_coloring_tournaments_3_colors :
  GC.digraph.AX_majority_coloring_digraphs_3_colors.main.AX_majority_coloring_digraphs_3_colors ->
  GC.digraph.AX_majority_coloring_tournaments_3_colors.main.AX_majority_coloring_tournaments_3_colors).
Print Assumptions
  AX_majority_coloring_digraphs_3_colors_implies_AX_majority_coloring_tournaments_3_colors.
