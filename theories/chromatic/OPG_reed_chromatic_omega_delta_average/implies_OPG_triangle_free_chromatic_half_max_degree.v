(** * Reed's conjecture implies the bound ⌈Δ/2⌉ + 2 for triangle-free graphs

A triangle-free graph G has clique number at most 2, so Reed's bound 2 χ(G) <= Δ(G) + 1 + ω(G) + 1
gives 2 χ(G) <= Δ(G) + 4, that is χ(G) <= ⌊Δ(G)/2⌋ + 2 <= ⌈Δ(G)/2⌉ + 2.  Reed's conjecture is
stated for nonempty graphs; the empty graph has chromatic number 0.

The implication is mentioned in the Open Problem Garden, and is the edge e005 of relations.json in
graph-conjectures.  It was formalized in graph-theory-rocq (chromatic-theory/theories/conjectures/implications_U8.v). *)

From GraphTheory Require Import digraph sgraph coloring.
From mathcomp Require Import boot zify_ssreflect.
From GC.GraphLib Require Import chromatic(triangle_free_omega).
From GC.chromatic.OPG_reed_chromatic_omega_delta_average Require Import
  main(OPG_reed_chromatic_omega_delta_average).
From GC.chromatic.OPG_triangle_free_chromatic_half_max_degree Require Import
  main(OPG_triangle_free_chromatic_half_max_degree).

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Theorem OPG_reed_chromatic_omega_delta_average_implies_OPG_triangle_free_chromatic_half_max_degree :
  OPG_reed_chromatic_omega_delta_average -> OPG_triangle_free_chromatic_half_max_degree.
Proof.
move=> R G tf; have [G0|Gpos] := posnP #|G|.
  by rewrite -cardsT in G0; rewrite (cards0_eq G0) chi0.
have : 2 * χ([set: G]) <= main.Delta G + 1 + ω([set: G]) + 1 := R G Gpos.
have := triangle_free_omega tf; rewrite /main.ceil_div; lia.
Qed.

Check (OPG_reed_chromatic_omega_delta_average_implies_OPG_triangle_free_chromatic_half_max_degree :
  GC.chromatic.OPG_reed_chromatic_omega_delta_average.main.OPG_reed_chromatic_omega_delta_average ->
  GC.chromatic.OPG_triangle_free_chromatic_half_max_degree.main.OPG_triangle_free_chromatic_half_max_degree).
Print Assumptions OPG_reed_chromatic_omega_delta_average_implies_OPG_triangle_free_chromatic_half_max_degree.
