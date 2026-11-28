(** * The fractional Hadwiger conjecture implies the seagull problem

Composition of the implications of the fractional Hadwiger conjecture to n <= t α(G) for
K_{t+1}-minor-free graphs, and of the latter to the seagull problem (its case α(G) <= 2).

The implication is the edge e042 of relations.json in graph-conjectures.  It was formalized in
graph-theory-rocq ([fractional_hadwiger_implies_seagull], directly from n <= had(G) α(G)). *)

From GC.extremal.OPG_hadwiger_fractional_chromatic_minor Require Import
  main(OPG_hadwiger_fractional_chromatic_minor).
From GC.minor.OPG_seagull_independence_2_clique_minor_half_n Require Import
  main(OPG_seagull_independence_2_clique_minor_half_n).
From GC.extremal.OPG_hadwiger_fractional_chromatic_minor Require Import
  implies_AX_kt_minor_free_independence_n_over_t.
From GC.minor.AX_kt_minor_free_independence_n_over_t Require Import
  implies_OPG_seagull_independence_2_clique_minor_half_n.

Theorem OPG_hadwiger_fractional_chromatic_minor_implies_OPG_seagull_independence_2_clique_minor_half_n :
  OPG_hadwiger_fractional_chromatic_minor -> OPG_seagull_independence_2_clique_minor_half_n.
Proof.
intro FH.
apply AX_kt_minor_free_independence_n_over_t_implies_OPG_seagull_independence_2_clique_minor_half_n.
exact (OPG_hadwiger_fractional_chromatic_minor_implies_AX_kt_minor_free_independence_n_over_t FH).
Qed.

Check (OPG_hadwiger_fractional_chromatic_minor_implies_OPG_seagull_independence_2_clique_minor_half_n :
  GC.extremal.OPG_hadwiger_fractional_chromatic_minor.main.OPG_hadwiger_fractional_chromatic_minor ->
  GC.minor.OPG_seagull_independence_2_clique_minor_half_n.main.OPG_seagull_independence_2_clique_minor_half_n).
Print Assumptions
  OPG_hadwiger_fractional_chromatic_minor_implies_OPG_seagull_independence_2_clique_minor_half_n.
