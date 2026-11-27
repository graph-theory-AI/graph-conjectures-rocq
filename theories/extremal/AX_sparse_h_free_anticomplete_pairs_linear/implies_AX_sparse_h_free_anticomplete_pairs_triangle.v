(** * Conjecture 1.4 of Chudnovsky, Fox, Scott, Seymour and Spirkl implies its case H = K_3

The case H = K_3 of the conjecture is an instance of the conjecture for every graph H.

The implication is the edge e076 of relations.json in graph-conjectures.  It was formalized in
graph-theory-rocq (extremal-graph-theory/theories/conjectures/implications_X223.v). *)

From GraphTheory Require Import digraph sgraph.
From mathcomp Require Import boot.
From GC.extremal.AX_sparse_h_free_anticomplete_pairs_linear Require Import
  main(AX_sparse_h_free_anticomplete_pairs_linear).
From GC.extremal.AX_sparse_h_free_anticomplete_pairs_triangle Require Import
  main(AX_sparse_h_free_anticomplete_pairs_triangle).

Theorem AX_sparse_h_free_anticomplete_pairs_linear_implies_AX_sparse_h_free_anticomplete_pairs_triangle :
  AX_sparse_h_free_anticomplete_pairs_linear -> AX_sparse_h_free_anticomplete_pairs_triangle.
Proof. exact: (fun h => h 'K_3). Qed.

Check (AX_sparse_h_free_anticomplete_pairs_linear_implies_AX_sparse_h_free_anticomplete_pairs_triangle :
  GC.extremal.AX_sparse_h_free_anticomplete_pairs_linear.main.AX_sparse_h_free_anticomplete_pairs_linear ->
  GC.extremal.AX_sparse_h_free_anticomplete_pairs_triangle.main.AX_sparse_h_free_anticomplete_pairs_triangle).
Print Assumptions AX_sparse_h_free_anticomplete_pairs_linear_implies_AX_sparse_h_free_anticomplete_pairs_triangle.
