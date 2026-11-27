(** * n <= t α(G) for K_{t+1}-minor-free graphs implies the seagull problem

Let G be a graph on n vertices with α(G) <= 2, and m = ⌈n/2⌉.  If m <= 1, a K_m minor is a vertex
or nothing.  Otherwise, if G had no K_m minor, the hypothesis with t = m - 1 would give
n <= 2 (m - 1) < n.  Minors are decidable, hence G has a K_m minor.

The implication is the edge e043 of relations.json in graph-conjectures.  It was formalized in
graph-theory-rocq ([hadwiger_independence_minor_implies_seagull]). *)

From GraphTheory Require Import digraph sgraph coloring minor.
From mathcomp Require Import boot.
From GC.GraphLib Require Import minor.
From GC.minor.AX_kt_minor_free_independence_n_over_t Require Import
  main(AX_kt_minor_free_independence_n_over_t).
From GC.minor.OPG_seagull_independence_2_clique_minor_half_n Require Import
  main(OPG_seagull_independence_2_clique_minor_half_n).

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Abbreviation ceil_div := main.ceil_div.

Theorem AX_kt_minor_free_independence_n_over_t_implies_OPG_seagull_independence_2_clique_minor_half_n :
  AX_kt_minor_free_independence_n_over_t -> OPG_seagull_independence_2_clique_minor_half_n.
Proof.
move=> KT G /card_gt0P[x _] a2; set m := ceil_div #|G| 2.
have [m1|m2] := leqP m 1.
  apply: minor_K_le m1 _; apply: (@minor_of_clique _ [set x]); [by rewrite cards1 | exact: clique1].
case: (minorP G 'K_m) => // nm; exfalso.
have m0 : 0 < m.-1 by rewrite -ltnS prednK // ltnW.
have := KT m.-1 _ G m0 erefl; rewrite prednK ?(ltnW m2) // => /(_ nm); apply/negP.
rewrite -ltnNge (leq_ltn_trans (leq_mul (leqnn _) a2)) // -subn1 mulnBl ltn_subLR.
  by rewrite leq_mul2r ltnW.
by rewrite addnC addn2 ltnS /m /ceil_div addn2 subn1 /= leq_divM.
Qed.

Check (AX_kt_minor_free_independence_n_over_t_implies_OPG_seagull_independence_2_clique_minor_half_n :
  GC.minor.AX_kt_minor_free_independence_n_over_t.main.AX_kt_minor_free_independence_n_over_t ->
  GC.minor.OPG_seagull_independence_2_clique_minor_half_n.main.OPG_seagull_independence_2_clique_minor_half_n).
Print Assumptions
  AX_kt_minor_free_independence_n_over_t_implies_OPG_seagull_independence_2_clique_minor_half_n.
