(** * Every forest is multibounding implies the polynomial τ_d bound for excluded paths

The path P_k is a forest, hence it is multibounding: for every d >= 1 there are c and e such that
χ(G) <= c s^e for every P_k-free graph G with no subgraph K_d(s), for all s >= 1.  If τ_d(G) = t,
then G has no subgraph K_d(t+1), hence χ(G) <= c (t+1)^e, which is a polynomial in t.

This implication is not in graph-conjectures.  It was formalized in graph-theory-rocq
(chromatic-theory/theories/conjectures/implications_X238.v). *)

From GraphTheory Require Import digraph sgraph coloring.
From mathcomp Require Import boot ssralg poly.
From GC.chromatic.AX_forest_free_multibounding_chi_bound Require Import
  main(AX_forest_free_multibounding_chi_bound).
From GC.chromatic.AX_path_free_polynomial_chi_tau_d Require Import
  main(AX_path_free_polynomial_chi_tau_d).
From GC.GraphLib Require Import cycle(path_graph_forest).

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Theorem AX_forest_free_multibounding_chi_bound_implies_AX_path_free_polynomial_chi_tau_d :
  AX_forest_free_multibounding_chi_bound -> AX_path_free_polynomial_chi_tau_d.
Proof.
move=> MB k d d1; have [c [e He]] := MB _ (@path_graph_forest k).
exists (c d *: ('X + 1) ^+ e d : {poly nat})%R => G t free [_ tmax].
rewrite -/(horner _ t) hornerZ horner_exp hornerD hornerX hornerC [(t + 1)%R]addn1.
by apply: He => // sub; have := tmax _ sub; rewrite ltnn.
Qed.

Check (AX_forest_free_multibounding_chi_bound_implies_AX_path_free_polynomial_chi_tau_d :
  GC.chromatic.AX_forest_free_multibounding_chi_bound.main.AX_forest_free_multibounding_chi_bound ->
  GC.chromatic.AX_path_free_polynomial_chi_tau_d.main.AX_path_free_polynomial_chi_tau_d).
Print Assumptions AX_forest_free_multibounding_chi_bound_implies_AX_path_free_polynomial_chi_tau_d.
