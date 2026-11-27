(** * Hadwiger's conjecture implies the seagull problem

Let G be a graph on n vertices with α(G) <= 2.  The colour classes of a colouring are stable sets,
hence n <= χ(G) α(G) <= 2 χ(G), that is ⌈n/2⌉ <= χ(G).  By Hadwiger's conjecture, G has a K_χ(G)
minor, hence a K_⌈n/2⌉ minor.

The implication is the edge e224 of relations.json in graph-conjectures.  It was formalized in
graph-theory-rocq ([hadwiger_chromatic_clique_minor_statement_implies_seagull_statement]). *)

From GraphTheory Require Import digraph sgraph coloring minor.
From mathcomp Require Import boot.
From GC.GraphLib Require Import chromatic(card_le_chi_alpha).
From GC.minor.BM_hadwiger_minor_chromatic Require Import main(BM_hadwiger_minor_chromatic).
From GC.minor.OPG_seagull_independence_2_clique_minor_half_n Require Import
  main(OPG_seagull_independence_2_clique_minor_half_n).

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Abbreviation ceil_div := main.ceil_div.

Theorem BM_hadwiger_minor_chromatic_implies_OPG_seagull_independence_2_clique_minor_half_n :
  BM_hadwiger_minor_chromatic -> OPG_seagull_independence_2_clique_minor_half_n.
Proof.
move=> Had G _ a2; apply: minor_trans (Had _ G erefl) _.
apply: (@minor_of_clique _ [set: 'K_(χ([set: G]))]); last exact: Kn_clique.
rewrite cardsT card_ord /ceil_div addn2 subn1 /= -ltnS ltn_divLR // mulSn add2n !ltnS.
by apply: leq_trans (card_le_chi_alpha G) _; rewrite leq_mul2l a2 orbT.
Qed.

Check (BM_hadwiger_minor_chromatic_implies_OPG_seagull_independence_2_clique_minor_half_n :
  GC.minor.BM_hadwiger_minor_chromatic.main.BM_hadwiger_minor_chromatic ->
  GC.minor.OPG_seagull_independence_2_clique_minor_half_n.main.OPG_seagull_independence_2_clique_minor_half_n).
Print Assumptions
  BM_hadwiger_minor_chromatic_implies_OPG_seagull_independence_2_clique_minor_half_n.
