(** * η-boundedness of H-free graphs for every forest H implies it for H = P_t

The path P_t is a forest.

This is the edge e012 of relations.json in graph-conjectures (arXiv:2302.04986, Conjecture 1.8
specialised to H = P_t).  It was formalized in graph-theory-rocq
(packing-theory/theories/conjectures/implications_X226.v). *)

From GraphTheory Require Import digraph sgraph.
From mathcomp Require Import boot.
From GC.packing.AX_hitting_max_stable_sets_forest_free Require Import
  main(AX_hitting_max_stable_sets_forest_free).
From GC.packing.AX_hitting_max_stable_sets_pt_free Require Import
  main(AX_hitting_max_stable_sets_pt_free).
From GC.GraphLib Require Import cycle(path_graph_forest).

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Theorem AX_hitting_max_stable_sets_forest_free_implies_AX_hitting_max_stable_sets_pt_free :
  AX_hitting_max_stable_sets_forest_free -> AX_hitting_max_stable_sets_pt_free.
Proof. by move=> P t _; apply: P; exact: path_graph_forest. Qed.

Check (AX_hitting_max_stable_sets_forest_free_implies_AX_hitting_max_stable_sets_pt_free :
  GC.packing.AX_hitting_max_stable_sets_forest_free.main.AX_hitting_max_stable_sets_forest_free ->
  GC.packing.AX_hitting_max_stable_sets_pt_free.main.AX_hitting_max_stable_sets_pt_free).
Print Assumptions
  AX_hitting_max_stable_sets_forest_free_implies_AX_hitting_max_stable_sets_pt_free.
