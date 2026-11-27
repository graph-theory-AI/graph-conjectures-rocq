(** * Bounded tree-independence number of (even hole, diamond)-free graphs implies bounded
      treewidth of (even hole, K_4, diamond)-free graphs

Let k bound the tree-independence number of (even hole, diamond)-free graphs.  An (even hole,
K_4, diamond)-free graph G has a tree decomposition whose bags have independence number at most
k, and its bags have no clique of size 4.  By Ramsey's theorem, the bags have at most N vertices,
for some N depending only on k, and G has treewidth less than N.

The implication is the edge e050 of relations.json in graph-conjectures.  It was formalized in
graph-theory-rocq (minor-theory/theories/conjectures/implications_X42.v). *)

From GraphTheory Require Import preliminaries digraph sgraph coloring treewidth.
From mathcomp Require Import boot.
From GC.GraphLib Require Import ramsey.
From GC.minor.AX_even_hole_diamond_free_tree_independence Require Import
  main(AX_even_hole_diamond_free_tree_independence).
From GC.minor.AX_even_hole_k4_diamond_free_treewidth Require Import
  main(AX_even_hole_k4_diamond_free_treewidth).

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Theorem AX_even_hole_diamond_free_tree_independence_implies_AX_even_hole_k4_diamond_free_treewidth :
  AX_even_hole_diamond_free_tree_independence -> AX_even_hole_k4_diamond_free_treewidth.
Proof.
case=> k tind; have [N HN] := ramsey_bound 4 k.
exists N => G eh noK4 nodiamond; have [T [D [dec aD]]] := tind G eh nodiamond.
exists T, D; split=> //; apply/bigmax_leqP => t _; apply: leqW; apply: HN (aD t) _.
apply: leq_ltn_trans (sub_omega (subsetT _)) _.
by rewrite ltnNge; apply/negP => /has_induced_copy_Kn.
Qed.

Check (AX_even_hole_diamond_free_tree_independence_implies_AX_even_hole_k4_diamond_free_treewidth :
  GC.minor.AX_even_hole_diamond_free_tree_independence.main.AX_even_hole_diamond_free_tree_independence ->
  GC.minor.AX_even_hole_k4_diamond_free_treewidth.main.AX_even_hole_k4_diamond_free_treewidth).
Print Assumptions AX_even_hole_diamond_free_tree_independence_implies_AX_even_hole_k4_diamond_free_treewidth.
