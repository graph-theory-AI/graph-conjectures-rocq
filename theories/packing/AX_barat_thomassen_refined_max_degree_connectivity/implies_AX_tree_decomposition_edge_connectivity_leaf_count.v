(** * Tree decompositions: the maximum-degree version implies the leaf version

The two conjectures differ only in the parameter of the edge-connectivity: the maximum degree Δ_T
of the tree T, or its number of leaves.  A tree has at least Δ_T leaves, and the two hypotheses on
G are weaker for smaller values of the parameters.  Hence, if f is a function for the first
conjecture, the function m ↦ max_{d ≤ m} f(d) is a function for the second one.

The implication is the edge e066 of relations.json in graph-conjectures.  It was formalized in
graph-theory-rocq (packing-theory/theories/conjectures/implications_X48.v). *)

From GraphTheory Require Import digraph sgraph.
From mathcomp Require Import boot.
From GC.GraphLib Require Import cycle.
From GC.packing.AX_barat_thomassen_refined_max_degree_connectivity Require Import
  main(AX_barat_thomassen_refined_max_degree_connectivity).
From GC.packing.AX_tree_decomposition_edge_connectivity_leaf_count Require Import
  main(AX_tree_decomposition_edge_connectivity_leaf_count).

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Theorem AX_barat_thomassen_refined_max_degree_connectivity_implies_AX_tree_decomposition_edge_connectivity_leaf_count :
  AX_barat_thomassen_refined_max_degree_connectivity ->
  AX_tree_decomposition_edge_connectivity_leaf_count.
Proof.
case=> f Hf; exists (fun m => \max_(d < m.+1) f d) => T G treeT ET conn deg dvd.
have le_max d m : d <= m -> f d <= \max_(i < m.+1) f i.
  by rewrite -ltnS => dm; apply: (leq_bigmax (Ordinal dm)).
apply: Hf => // [S S0 ST|v].
  by apply: leq_trans (conn S S0 ST); apply/le_max/forest_Delta_le_leaves; case: treeT.
exact: leq_trans (le_max _ _ (leqnn _)) (deg v).
Qed.

Check (AX_barat_thomassen_refined_max_degree_connectivity_implies_AX_tree_decomposition_edge_connectivity_leaf_count :
  GC.packing.AX_barat_thomassen_refined_max_degree_connectivity.main.AX_barat_thomassen_refined_max_degree_connectivity ->
  GC.packing.AX_tree_decomposition_edge_connectivity_leaf_count.main.AX_tree_decomposition_edge_connectivity_leaf_count).
Print Assumptions AX_barat_thomassen_refined_max_degree_connectivity_implies_AX_tree_decomposition_edge_connectivity_leaf_count.
