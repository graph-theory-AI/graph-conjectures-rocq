(** * K_6 minors for minimum degree 6 and maximum degree 8 imply them for 6-regular graphs

A 6-regular graph has minimum degree 6 and maximum degree 6 <= 8.

The implication is the edge e045 of relations.json in graph-conjectures.  It was formalized in
graph-theory-rocq (minor-theory/theories/conjectures/implications_X5.v). *)

From GraphTheory Require Import digraph sgraph minor.
From mathcomp Require Import boot.
From GC.minor.AX_k6_minor_min_6_max_8 Require Import main(AX_k6_minor_min_6_max_8).
From GC.minor.AX_k6_minor_6_regular_graphs Require Import main(AX_k6_minor_6_regular_graphs).

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Theorem AX_k6_minor_min_6_max_8_implies_AX_k6_minor_6_regular_graphs :
  AX_k6_minor_min_6_max_8 -> AX_k6_minor_6_regular_graphs.
Proof.
move=> H G G0 reg; apply: H => // [v|]; first by rewrite reg.
by apply/bigmax_leqP => v _; rewrite reg.
Qed.

Check (AX_k6_minor_min_6_max_8_implies_AX_k6_minor_6_regular_graphs :
  GC.minor.AX_k6_minor_min_6_max_8.main.AX_k6_minor_min_6_max_8 ->
  GC.minor.AX_k6_minor_6_regular_graphs.main.AX_k6_minor_6_regular_graphs).
Print Assumptions AX_k6_minor_min_6_max_8_implies_AX_k6_minor_6_regular_graphs.
