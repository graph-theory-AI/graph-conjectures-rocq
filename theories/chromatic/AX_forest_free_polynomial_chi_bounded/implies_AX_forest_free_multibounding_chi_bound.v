(** * Polynomial χ-boundedness of forest-free graphs implies that every forest is multibounding

The proposition is identical to the one stating that every forest is good, which implies that
every forest is multibounding.

This is the edge e034 of relations.json in graph-conjectures.  It was formalized in
graph-theory-rocq (chromatic-theory/theories/conjectures/implications_X218.v). *)

From mathcomp Require Import boot.
From GC.chromatic.AX_forest_free_polynomial_chi_bounded Require Import
  main(AX_forest_free_polynomial_chi_bounded).
From GC.chromatic.AX_forest_free_multibounding_chi_bound Require Import
  main(AX_forest_free_multibounding_chi_bound).
From GC.chromatic.AX_forest_free_polynomial_chi_good Require Import
  implies_AX_forest_free_multibounding_chi_bound.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Theorem AX_forest_free_polynomial_chi_bounded_implies_AX_forest_free_multibounding_chi_bound :
  AX_forest_free_polynomial_chi_bounded -> AX_forest_free_multibounding_chi_bound.
Proof.
exact: AX_forest_free_polynomial_chi_good_implies_AX_forest_free_multibounding_chi_bound.
Qed.

Check (AX_forest_free_polynomial_chi_bounded_implies_AX_forest_free_multibounding_chi_bound :
  GC.chromatic.AX_forest_free_polynomial_chi_bounded.main.AX_forest_free_polynomial_chi_bounded ->
  GC.chromatic.AX_forest_free_multibounding_chi_bound.main.AX_forest_free_multibounding_chi_bound).
Print Assumptions AX_forest_free_polynomial_chi_bounded_implies_AX_forest_free_multibounding_chi_bound.
