(** * 1/k-majority colourings with k+1 colours give majority 3-colourings

Conjecture 9 at k = 2 is Conjecture 2: a 1/2-majority colouring with 3 colours is a majority
3-colouring.

The implication is the edge e018 of relations.json in graph-conjectures.  It was formalized in
graph-theory-rocq (digraph-theory/theories/conjectures/implications_X1.v). *)

From GraphTheory Require Import digraph.
From mathcomp Require Import boot.
From GC.digraph.AX_majority_coloring_digraphs_1_over_k Require Import
  main(AX_majority_coloring_digraphs_1_over_k).
From GC.digraph.AX_majority_coloring_digraphs_3_colors Require Import
  main(AX_majority_coloring_digraphs_3_colors).

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Theorem AX_majority_coloring_digraphs_1_over_k_implies_AX_majority_coloring_digraphs_3_colors :
  AX_majority_coloring_digraphs_1_over_k -> AX_majority_coloring_digraphs_3_colors.
Proof. by move=> H D; exact: H. Qed.

Check (AX_majority_coloring_digraphs_1_over_k_implies_AX_majority_coloring_digraphs_3_colors :
  GC.digraph.AX_majority_coloring_digraphs_1_over_k.main.AX_majority_coloring_digraphs_1_over_k ->
  GC.digraph.AX_majority_coloring_digraphs_3_colors.main.AX_majority_coloring_digraphs_3_colors).
Print Assumptions
  AX_majority_coloring_digraphs_1_over_k_implies_AX_majority_coloring_digraphs_3_colors.
