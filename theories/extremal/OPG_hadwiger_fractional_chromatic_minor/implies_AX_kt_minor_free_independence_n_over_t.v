(** * The fractional Hadwiger conjecture implies n <= t α(G) for K_{t+1}-minor-free graphs

Let G be a nonempty graph on n vertices with no K_{t+1} minor.  Its Hadwiger number h is at most t.
In a b-fold colouring of G with a colours, the a colour classes are stable sets and cover every
vertex b times, hence n b <= a α(G), that is n <= χ_f(G) α(G).  Part (a) of the fractional
Hadwiger conjecture, χ_f(G) <= h, gives n <= t α(G).  The empty graph is trivial.

To apply the conjecture, χ_f(G), had(G) and had_f(G) must exist: the last two are the optima of
linear programs, which are attained (GraphLib/fractional.v).

The implication is the edge e003 of relations.json in graph-conjectures.  It was formalized in
graph-theory-rocq ([fractional_hadwiger_implies_hadwiger_independence_minor]). *)

From GraphTheory Require Import digraph sgraph coloring minor.
From mathcomp Require Import boot order ssralg ssrnum rat.
From GC.GraphLib Require Import minor fractional.
From GC.extremal.OPG_hadwiger_fractional_chromatic_minor Require Import
  main(OPG_hadwiger_fractional_chromatic_minor).
From GC.minor.AX_kt_minor_free_independence_n_over_t Require Import
  main(AX_kt_minor_free_independence_n_over_t).

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.Theory GRing.Theory Num.Theory.

Theorem OPG_hadwiger_fractional_chromatic_minor_implies_AX_kt_minor_free_independence_n_over_t :
  OPG_hadwiger_fractional_chromatic_minor -> AX_kt_minor_free_independence_n_over_t.
Proof.
move=> FH t n G _ <- nK; case: (posnP #|G|) => [-> //|G0].
have [xf hxf] := fractional_chromatic_number_exists G.
have [hf hhf] := fractional_hadwiger_number_exists G.
have [h hh] := hadwiger_number_exists G.
have [xh _ _] := FH G xf hf h G0 hxf hh hhf.
have ht : h <= t by rewrite leqNgt; apply/negP => th; apply/nK/(minor_K_le th); case: hh.
rewrite -(ler_nat rat) natrM; apply: le_trans (card_le_fractional_chromatic_alpha hxf) _.
by rewrite ler_wpM2r // (le_trans xh) // ler_nat.
Qed.

Check (OPG_hadwiger_fractional_chromatic_minor_implies_AX_kt_minor_free_independence_n_over_t :
  GC.extremal.OPG_hadwiger_fractional_chromatic_minor.main.OPG_hadwiger_fractional_chromatic_minor ->
  GC.minor.AX_kt_minor_free_independence_n_over_t.main.AX_kt_minor_free_independence_n_over_t).
Print Assumptions
  OPG_hadwiger_fractional_chromatic_minor_implies_AX_kt_minor_free_independence_n_over_t.
