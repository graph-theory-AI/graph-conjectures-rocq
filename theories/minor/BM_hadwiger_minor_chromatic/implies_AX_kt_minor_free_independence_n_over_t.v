(** * Hadwiger's conjecture implies n <= t α(G) for K_{t+1}-minor-free graphs

Let G be a graph on n vertices with no K_{t+1} minor.  By Hadwiger's conjecture, G has a K_χ(G)
minor, hence χ(G) <= t.  The colour classes of a colouring are stable sets, hence
n <= χ(G) α(G) <= t α(G).

The implication is the edge e240 of relations.json in graph-conjectures.  It was formalized in
graph-theory-rocq
([hadwiger_chromatic_clique_minor_statement_implies_hadwiger_independence_minor_statement]). *)

From GraphTheory Require Import digraph sgraph coloring minor.
From mathcomp Require Import boot.
From GC.GraphLib Require Import chromatic(card_le_chi_alpha).
From GC.minor.BM_hadwiger_minor_chromatic Require Import main(BM_hadwiger_minor_chromatic).
From GC.minor.AX_kt_minor_free_independence_n_over_t Require Import
  main(AX_kt_minor_free_independence_n_over_t).

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Theorem BM_hadwiger_minor_chromatic_implies_AX_kt_minor_free_independence_n_over_t :
  BM_hadwiger_minor_chromatic -> AX_kt_minor_free_independence_n_over_t.
Proof.
move=> Had t n G _ <- nK; apply: leq_trans (card_le_chi_alpha G) _; rewrite leq_mul2r.
apply/orP; right; rewrite leqNgt; apply/negP => tchi; apply/nK/(minor_trans (Had _ G erefl)).
apply: (@minor_of_clique _ [set: 'K_(χ([set: G]))]); last exact: Kn_clique.
by rewrite cardsT card_ord.
Qed.

Check (BM_hadwiger_minor_chromatic_implies_AX_kt_minor_free_independence_n_over_t :
  GC.minor.BM_hadwiger_minor_chromatic.main.BM_hadwiger_minor_chromatic ->
  GC.minor.AX_kt_minor_free_independence_n_over_t.main.AX_kt_minor_free_independence_n_over_t).
Print Assumptions BM_hadwiger_minor_chromatic_implies_AX_kt_minor_free_independence_n_over_t.
