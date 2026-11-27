(** * The polynomial Gyárfás-Sumner conjecture with bound ω^c implies the version with c ω^d

The bound ω(G)^c is the bound c' ω(G)^d with c' = 1 and d = c.

This implication is not in graph-conjectures.  It was formalized in graph-theory-rocq
(chromatic-theory/theories/conjectures/implications_X65.v). *)

From GraphTheory Require Import digraph sgraph coloring.
From mathcomp Require Import boot.
From GC.chromatic.AX_forest_free_polynomial_chi_omega_power Require Import
  main(AX_forest_free_polynomial_chi_omega_power).
From GC.chromatic.AX_forest_free_polynomial_chi_bounded Require Import
  main(AX_forest_free_polynomial_chi_bounded).

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Theorem AX_forest_free_polynomial_chi_omega_power_implies_AX_forest_free_polynomial_chi_bounded :
  AX_forest_free_polynomial_chi_omega_power -> AX_forest_free_polynomial_chi_bounded.
Proof. by move=> P H Hf; have [c [_ h]] := P H Hf; exists 1, c => G /h; rewrite mul1n. Qed.

Check (AX_forest_free_polynomial_chi_omega_power_implies_AX_forest_free_polynomial_chi_bounded :
  GC.chromatic.AX_forest_free_polynomial_chi_omega_power.main.AX_forest_free_polynomial_chi_omega_power ->
  GC.chromatic.AX_forest_free_polynomial_chi_bounded.main.AX_forest_free_polynomial_chi_bounded).
Print Assumptions AX_forest_free_polynomial_chi_omega_power_implies_AX_forest_free_polynomial_chi_bounded.
