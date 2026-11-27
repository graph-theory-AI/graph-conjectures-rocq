(** * Polynomial χ-boundedness of forest-free graphs implies the Gyárfás-Sumner conjecture

A tree is a forest, and a polynomial χ-bounding function is a χ-bounding function.

This is the edge e009 of relations.json in graph-conjectures.  It was formalized in
graph-theory-rocq (chromatic-theory/theories/conjectures/implications_U8.v). *)

From GraphTheory Require Import digraph sgraph coloring.
From mathcomp Require Import boot.
From GC.chromatic.AX_forest_free_polynomial_chi_bounded Require Import
  main(AX_forest_free_polynomial_chi_bounded).
From GC.chromatic.OPG_gyarfas_sumner_forbidden_tree_chi_bounded Require Import
  main(OPG_gyarfas_sumner_forbidden_tree_chi_bounded).

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Theorem AX_forest_free_polynomial_chi_bounded_implies_OPG_gyarfas_sumner_forbidden_tree_chi_bounded :
  AX_forest_free_polynomial_chi_bounded -> OPG_gyarfas_sumner_forbidden_tree_chi_bounded.
Proof. by move=> P T [Tf _]; have [c [d h]] := P T Tf; exists (fun w => c * w ^ d). Qed.

Check (AX_forest_free_polynomial_chi_bounded_implies_OPG_gyarfas_sumner_forbidden_tree_chi_bounded :
  GC.chromatic.AX_forest_free_polynomial_chi_bounded.main.AX_forest_free_polynomial_chi_bounded ->
  GC.chromatic.OPG_gyarfas_sumner_forbidden_tree_chi_bounded.main.OPG_gyarfas_sumner_forbidden_tree_chi_bounded).
Print Assumptions AX_forest_free_polynomial_chi_bounded_implies_OPG_gyarfas_sumner_forbidden_tree_chi_bounded.
