(** * Every forest is good implies that the disjoint union of two good trees is good

The disjoint union of two trees is a forest, hence it is good.  The hypotheses that the two trees
are good are not used.

This is the edge e036 of relations.json in graph-conjectures.  It was formalized in
graph-theory-rocq (chromatic-theory/theories/conjectures/implications_X66.v). *)

From GraphTheory Require Import digraph sgraph coloring treewidth.
From mathcomp Require Import boot.
From GC.chromatic.AX_forest_free_polynomial_chi_good Require Import
  main(AX_forest_free_polynomial_chi_good).
From GC.chromatic.AX_poly_chi_bounded_trees_disjoint_union Require Import
  main(AX_poly_chi_bounded_trees_disjoint_union).

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Theorem AX_forest_free_polynomial_chi_good_implies_AX_poly_chi_bounded_trees_disjoint_union :
  AX_forest_free_polynomial_chi_good -> AX_poly_chi_bounded_trees_disjoint_union.
Proof.
by move=> P H1 H2 [f1 _] [f2 _] _ _; apply: P; exact: (@join_is_forest (Forest f1) (Forest f2)).
Qed.

Check (AX_forest_free_polynomial_chi_good_implies_AX_poly_chi_bounded_trees_disjoint_union :
  GC.chromatic.AX_forest_free_polynomial_chi_good.main.AX_forest_free_polynomial_chi_good ->
  GC.chromatic.AX_poly_chi_bounded_trees_disjoint_union.main.AX_poly_chi_bounded_trees_disjoint_union).
Print Assumptions AX_forest_free_polynomial_chi_good_implies_AX_poly_chi_bounded_trees_disjoint_union.
