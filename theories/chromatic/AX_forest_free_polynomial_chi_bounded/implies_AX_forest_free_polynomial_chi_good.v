(** * Two statements of the polynomial χ-boundedness of forest-free graphs

The two conjectures are stated in two papers (arXiv:2202.05557 and arXiv:2202.10412), and their
propositions are the same.

This is the edge e007 of relations.json in graph-conjectures (same conjecture).  The equivalence
was formalized in graph-theory-rocq (chromatic-theory/theories/conjectures/implications_X218.v). *)

From mathcomp Require Import boot.
From GC.chromatic.AX_forest_free_polynomial_chi_bounded Require Import
  main(AX_forest_free_polynomial_chi_bounded).
From GC.chromatic.AX_forest_free_polynomial_chi_good Require Import
  main(AX_forest_free_polynomial_chi_good).

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Theorem AX_forest_free_polynomial_chi_bounded_implies_AX_forest_free_polynomial_chi_good :
  AX_forest_free_polynomial_chi_bounded -> AX_forest_free_polynomial_chi_good.
Proof. exact: id. Qed.

Check (AX_forest_free_polynomial_chi_bounded_implies_AX_forest_free_polynomial_chi_good :
  GC.chromatic.AX_forest_free_polynomial_chi_bounded.main.AX_forest_free_polynomial_chi_bounded ->
  GC.chromatic.AX_forest_free_polynomial_chi_good.main.AX_forest_free_polynomial_chi_good).
Print Assumptions AX_forest_free_polynomial_chi_bounded_implies_AX_forest_free_polynomial_chi_good.
