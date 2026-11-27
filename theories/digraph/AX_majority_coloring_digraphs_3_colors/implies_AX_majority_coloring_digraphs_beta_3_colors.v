(** * Majority 3-colourings give 3-colourings with a constant β < 1

A majority 3-colouring has, at each vertex v, at most deg⁺(v)/2 out-neighbours of the colour of v:
this is the bound β deg⁺(v) with β = 1/2.

The implication is the edge e038 of relations.json in graph-conjectures.  It was formalized in
graph-theory-rocq (digraph-theory/theories/conjectures/implications_X45.v). *)

From GraphTheory Require Import digraph.
From mathcomp Require Import boot.
From GC.digraph.AX_majority_coloring_digraphs_3_colors Require Import
  main(AX_majority_coloring_digraphs_3_colors).
From GC.digraph.AX_majority_coloring_digraphs_beta_3_colors Require Import
  main(AX_majority_coloring_digraphs_beta_3_colors).

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Theorem AX_majority_coloring_digraphs_3_colors_implies_AX_majority_coloring_digraphs_beta_3_colors :
  AX_majority_coloring_digraphs_3_colors -> AX_majority_coloring_digraphs_beta_3_colors.
Proof.
by move=> H; exists 1, 2; split=> // D /H [col /forallP maj]; exists col => v; rewrite mul1n.
Qed.

Check (AX_majority_coloring_digraphs_3_colors_implies_AX_majority_coloring_digraphs_beta_3_colors :
  GC.digraph.AX_majority_coloring_digraphs_3_colors.main.AX_majority_coloring_digraphs_3_colors ->
  GC.digraph.AX_majority_coloring_digraphs_beta_3_colors.main.AX_majority_coloring_digraphs_beta_3_colors).
Print Assumptions
  AX_majority_coloring_digraphs_3_colors_implies_AX_majority_coloring_digraphs_beta_3_colors.
