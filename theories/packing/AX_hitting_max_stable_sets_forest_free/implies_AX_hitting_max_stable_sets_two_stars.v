(** * η-boundedness of H-free graphs for every forest H implies it for H = S_a ∪ S_b

A star is a forest, since all its edges contain the centre, and a disjoint union of two forests is a
forest.

This is the edge e013 of relations.json in graph-conjectures (arXiv:2302.04986, Conjecture 1.8
specialised to H = S_a ∪ S_b).  It was formalized in graph-theory-rocq
(packing-theory/theories/conjectures/implications_X226.v). *)

From GraphTheory Require Import digraph sgraph treewidth.
From mathcomp Require Import boot.
From GC.packing.AX_hitting_max_stable_sets_forest_free Require Import
  main(AX_hitting_max_stable_sets_forest_free).
From GC.packing.AX_hitting_max_stable_sets_two_stars Require Import
  main(AX_hitting_max_stable_sets_two_stars).
From GC.GraphLib Require Import cycle(star_forest).

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Theorem AX_hitting_max_stable_sets_forest_free_implies_AX_hitting_max_stable_sets_two_stars :
  AX_hitting_max_stable_sets_forest_free -> AX_hitting_max_stable_sets_two_stars.
Proof.
move=> P a b _ _; apply: P.
exact: (@join_is_forest (Forest (@star_forest a)) (Forest (@star_forest b))).
Qed.

Check (AX_hitting_max_stable_sets_forest_free_implies_AX_hitting_max_stable_sets_two_stars :
  GC.packing.AX_hitting_max_stable_sets_forest_free.main.AX_hitting_max_stable_sets_forest_free ->
  GC.packing.AX_hitting_max_stable_sets_two_stars.main.AX_hitting_max_stable_sets_two_stars).
Print Assumptions
  AX_hitting_max_stable_sets_forest_free_implies_AX_hitting_max_stable_sets_two_stars.
