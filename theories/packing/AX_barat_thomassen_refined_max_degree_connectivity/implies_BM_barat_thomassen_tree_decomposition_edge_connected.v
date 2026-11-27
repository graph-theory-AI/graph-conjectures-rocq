(** * Tree decompositions: the maximum-degree version implies the Barát-Thomassen conjecture

Let f be a function for the maximum-degree version, T a tree, and k = max(f(Δ_T), f(|E(T)|)).
Let G be a k-edge-connected graph whose number of edges is divisible by |E(T)|.  If G has no edge,
the empty family decomposes it.  Otherwise G has at least two vertices, so its minimum degree is
at least its edge-connectivity, hence at least f(|E(T)|), and |E(T)| > 0, as |E(T)| divides
|E(G)| > 0: the maximum-degree version applies.

The implication is the edge e208 of relations.json in graph-conjectures.  It was formalized in
graph-theory-rocq (atlas/theories/conjectures/implications_A1.v). *)

From GraphTheory Require Import digraph sgraph.
From mathcomp Require Import boot.
From GC.GraphLib Require Import cycle.
From GC.packing.AX_barat_thomassen_refined_max_degree_connectivity Require Import
  main(AX_barat_thomassen_refined_max_degree_connectivity, Delta).
From GC.cycle.BM_barat_thomassen_tree_decomposition_edge_connected Require Import
  main(BM_barat_thomassen_tree_decomposition_edge_connected).

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Theorem AX_barat_thomassen_refined_max_degree_connectivity_implies_BM_barat_thomassen_tree_decomposition_edge_connected :
  AX_barat_thomassen_refined_max_degree_connectivity ->
  BM_barat_thomassen_tree_decomposition_edge_connected.
Proof.
case=> f Hf T _ treeT; exists (maxn (f (Delta T)) (f #|E(T)|)) => G conn dvd.
have [E0|/set0Pn[_ /edgesP[x [y [_ xy]]]]] := eqVneq E(G) set0.
  by exists [::]; split => // e; rewrite E0 inE.
have G1 : 1 < #|G| by apply/card_gt1P; exists x, y; rewrite sg_edgeNeq.
apply: Hf => // [|S S0 ST|v].
- rewrite lt0n; apply: contraTneq dvd => ->; rewrite dvd0n cards_eq0.
  by apply/set0Pn; exists [set x; y]; rewrite in_edges.
- exact: leq_trans (leq_maxl _ _) (conn S S0 ST).
- exact: leq_trans (leq_maxr _ _) (edge_connected_min_degree G1 conn v).
Qed.

Check (AX_barat_thomassen_refined_max_degree_connectivity_implies_BM_barat_thomassen_tree_decomposition_edge_connected :
  GC.packing.AX_barat_thomassen_refined_max_degree_connectivity.main.AX_barat_thomassen_refined_max_degree_connectivity ->
  GC.cycle.BM_barat_thomassen_tree_decomposition_edge_connected.main.BM_barat_thomassen_tree_decomposition_edge_connected).
Print Assumptions AX_barat_thomassen_refined_max_degree_connectivity_implies_BM_barat_thomassen_tree_decomposition_edge_connected.
