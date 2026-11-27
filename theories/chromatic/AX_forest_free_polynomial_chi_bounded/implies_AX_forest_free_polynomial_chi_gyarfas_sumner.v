(** * Polynomial χ-boundedness of forest-free graphs implies its case of trees

A tree is a forest.

This is the edge e033 of relations.json in graph-conjectures.  It was formalized in
graph-theory-rocq (chromatic-theory/theories/conjectures/implications_X218.v). *)

From GraphTheory Require Import digraph sgraph coloring.
From mathcomp Require Import boot.
From GC.chromatic.AX_forest_free_polynomial_chi_bounded Require Import
  main(AX_forest_free_polynomial_chi_bounded).
From GC.chromatic.AX_forest_free_polynomial_chi_gyarfas_sumner Require Import
  main(AX_forest_free_polynomial_chi_gyarfas_sumner).

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Theorem AX_forest_free_polynomial_chi_bounded_implies_AX_forest_free_polynomial_chi_gyarfas_sumner :
  AX_forest_free_polynomial_chi_bounded -> AX_forest_free_polynomial_chi_gyarfas_sumner.
Proof. by move=> P T [Tf _]; exact: P. Qed.

Check (AX_forest_free_polynomial_chi_bounded_implies_AX_forest_free_polynomial_chi_gyarfas_sumner :
  GC.chromatic.AX_forest_free_polynomial_chi_bounded.main.AX_forest_free_polynomial_chi_bounded ->
  GC.chromatic.AX_forest_free_polynomial_chi_gyarfas_sumner.main.AX_forest_free_polynomial_chi_gyarfas_sumner).
Print Assumptions AX_forest_free_polynomial_chi_bounded_implies_AX_forest_free_polynomial_chi_gyarfas_sumner.
