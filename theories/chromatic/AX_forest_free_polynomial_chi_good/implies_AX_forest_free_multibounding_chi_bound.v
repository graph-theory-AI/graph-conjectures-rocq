(** * Every forest is good implies every forest is multibounding

Let H be a forest, and c, e such that χ(G) <= c ω(G)^e for every graph G with no induced H.  A
clique of size d t contains the complete d-partite graph K_d(t) with parts of size t as a subgraph.
Hence, if G has no subgraph K_d(t), then ω(G) < d t and χ(G) <= c d^e t^e.

This is the edge e171 of relations.json in graph-conjectures.  It was formalized in
graph-theory-rocq (chromatic-theory/theories/conjectures/implications_X218.v). *)

From GraphTheory Require Import digraph sgraph coloring.
From mathcomp Require Import boot.
From GC.chromatic.AX_forest_free_polynomial_chi_good Require Import
  main(AX_forest_free_polynomial_chi_good).
From GC.chromatic.AX_forest_free_multibounding_chi_bound Require Import
  main(AX_forest_free_multibounding_chi_bound).
From GC.GraphLib Require Import chromatic(clique_complete_multipartite).

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Theorem AX_forest_free_polynomial_chi_good_implies_AX_forest_free_multibounding_chi_bound :
  AX_forest_free_polynomial_chi_good -> AX_forest_free_multibounding_chi_bound.
Proof.
move=> P H Hf; have [c [e He]] := P H Hf.
exists (fun d => c * d ^ e), (fun _ => e) => d _ t G _ free nsub.
have w : ω([set: G]) <= d * t.
  by rewrite leqNgt; apply/negP => /ltnW/clique_complete_multipartite.
apply: leq_trans (He G free) _; rewrite -mulnA -expnMn leq_mul2l.
by apply/orP; right; elim: e {He} => // e IH; rewrite !expnS leq_mul.
Qed.

Check (AX_forest_free_polynomial_chi_good_implies_AX_forest_free_multibounding_chi_bound :
  GC.chromatic.AX_forest_free_polynomial_chi_good.main.AX_forest_free_polynomial_chi_good ->
  GC.chromatic.AX_forest_free_multibounding_chi_bound.main.AX_forest_free_multibounding_chi_bound).
Print Assumptions AX_forest_free_polynomial_chi_good_implies_AX_forest_free_multibounding_chi_bound.
