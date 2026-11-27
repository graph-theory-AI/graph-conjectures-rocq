(** * The list colouring analogue of Reed's conjecture implies Reed's conjecture

Every graph G has a choice number χ_l(G), and χ(G) <= χ_l(G): a graph that is k-choosable is
k-colourable, by giving every vertex the list of all k colours.  Hence the bound
χ_l(G) <= ⌈(Δ(G) + 1 + ω(G)) / 2⌉ implies χ(G) <= ⌈(Δ(G) + 1 + ω(G)) / 2⌉, which is Reed's bound.

The existence of the choice number is only proved in double negation form (it is the least k such
that G is k-choosable, and choosability quantifies over all types of colours); this suffices since
Reed's bound is a decidable statement.

The implication is the edge e004 of relations.json in graph-conjectures.  It was formalized in
graph-theory-rocq (chromatic-theory/theories/conjectures/implications_U1.v). *)

From GraphTheory Require Import digraph sgraph coloring.
From mathcomp Require Import boot zify_ssreflect.
From GC.GraphLib Require Import chromatic(choice_number_nn, chi_le_choosable).
From GC.chromatic.AX_list_chromatic_reed_bound Require Import main(AX_list_chromatic_reed_bound).
From GC.chromatic.OPG_reed_chromatic_omega_delta_average Require Import
  main(OPG_reed_chromatic_omega_delta_average).

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Theorem AX_list_chromatic_reed_bound_implies_OPG_reed_chromatic_omega_delta_average :
  AX_list_chromatic_reed_bound -> OPG_reed_chromatic_omega_delta_average.
Proof.
move=> LR G _; apply/negPn/negP => notR; apply: (@choice_number_nn G) => -[m chm].
have : m <= (main.Delta G + 1 + ω([set: G]) + 2 - 1) %/ 2 := LR G m chm.
by move: notR (chi_le_choosable chm.1); lia.
Qed.

Check (AX_list_chromatic_reed_bound_implies_OPG_reed_chromatic_omega_delta_average :
  GC.chromatic.AX_list_chromatic_reed_bound.main.AX_list_chromatic_reed_bound ->
  GC.chromatic.OPG_reed_chromatic_omega_delta_average.main.OPG_reed_chromatic_omega_delta_average).
Print Assumptions AX_list_chromatic_reed_bound_implies_OPG_reed_chromatic_omega_delta_average.
