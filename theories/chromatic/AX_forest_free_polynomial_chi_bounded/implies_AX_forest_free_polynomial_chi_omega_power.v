(** * The polynomial Gyárfás-Sumner conjecture with bound c ω^d implies the version with ω^c

Let G be a graph with χ(G) <= c ω(G)^d.  If ω(G) >= 2, then c < 2^c <= ω(G)^c, hence
χ(G) <= ω(G)^(c+d+1).  If ω(G) <= 1, then χ(G) = ω(G): the graph G has no vertex or no edge.

This implication is not in graph-conjectures.  It was formalized in graph-theory-rocq
(chromatic-theory/theories/conjectures/implications_X65.v). *)

From GraphTheory Require Import digraph sgraph coloring.
From mathcomp Require Import boot.
From GC.chromatic.AX_forest_free_polynomial_chi_bounded Require Import
  main(AX_forest_free_polynomial_chi_bounded).
From GC.chromatic.AX_forest_free_polynomial_chi_omega_power Require Import
  main(AX_forest_free_polynomial_chi_omega_power).
From GC.GraphLib Require Import chromatic(chi_omega_le1).

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Theorem AX_forest_free_polynomial_chi_bounded_implies_AX_forest_free_polynomial_chi_omega_power :
  AX_forest_free_polynomial_chi_bounded -> AX_forest_free_polynomial_chi_omega_power.
Proof.
move=> P H Hf; have [c [d h]] := P H Hf; exists (c + d).+1; split=> // G free.
have [w1|w2] := leqP ω([set: G]) 1.
  by rewrite chi_omega_le1 //; case: (ω(_)) w1 => [|[|]] //; rewrite exp1n.
apply: leq_trans (h G free) _; rewrite expnS expnD mulnA leq_mul2r; apply/orP; right.
exact: leq_trans (ltnW (ltn_expl c w2)) (leq_pmull _ (ltnW w2)).
Qed.

Check (AX_forest_free_polynomial_chi_bounded_implies_AX_forest_free_polynomial_chi_omega_power :
  GC.chromatic.AX_forest_free_polynomial_chi_bounded.main.AX_forest_free_polynomial_chi_bounded ->
  GC.chromatic.AX_forest_free_polynomial_chi_omega_power.main.AX_forest_free_polynomial_chi_omega_power).
Print Assumptions AX_forest_free_polynomial_chi_bounded_implies_AX_forest_free_polynomial_chi_omega_power.
