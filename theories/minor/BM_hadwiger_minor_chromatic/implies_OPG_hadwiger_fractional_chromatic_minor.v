(** * Hadwiger's conjecture implies the fractional Hadwiger conjecture

By Hadwiger's conjecture, G has a K_χ(G) minor.  Hence χ(G) <= had(G), and χ(G) <= had_f(G) (the
branch sets of the minor with weight 1).  A colouring with χ(G) colours is a 1-fold colouring,
hence χ_f(G) <= χ(G).  The three inequalities χ_f <= had, χ <= had_f and χ_f <= had_f follow.

The implication is the edge e223 of relations.json in graph-conjectures.  It was formalized in
graph-theory-rocq ([hadwiger_chromatic_clique_minor_implies_fractional_hadwiger]). *)

From GraphTheory Require Import digraph sgraph coloring minor.
From mathcomp Require Import boot order ssralg ssrnum ssrint rat.
From GC.GraphLib Require Import minor fractional.
From GC.minor.BM_hadwiger_minor_chromatic Require Import main(BM_hadwiger_minor_chromatic).
From GC.extremal.OPG_hadwiger_fractional_chromatic_minor Require Import
  main(OPG_hadwiger_fractional_chromatic_minor).

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.Theory GRing.Theory Num.Theory.

Theorem BM_hadwiger_minor_chromatic_implies_OPG_hadwiger_fractional_chromatic_minor :
  BM_hadwiger_minor_chromatic -> OPG_hadwiger_fractional_chromatic_minor.
Proof.
move=> Had G xf hf h _ hxf [_ hmax] hhf; have m := Had _ G erefl.
have c1 := fractional_chromatic_le_chi hxf.
have c2 := minor_le_fractional_hadwiger m hhf.
have c3 : (χ([set: G])%:Q <= h%:Q)%R by rewrite ler_nat; exact: hmax.
by split; [exact: le_trans c1 c3 | exact: c2 | exact: le_trans c1 c2].
Qed.

Check (BM_hadwiger_minor_chromatic_implies_OPG_hadwiger_fractional_chromatic_minor :
  GC.minor.BM_hadwiger_minor_chromatic.main.BM_hadwiger_minor_chromatic ->
  GC.extremal.OPG_hadwiger_fractional_chromatic_minor.main.OPG_hadwiger_fractional_chromatic_minor).
Print Assumptions BM_hadwiger_minor_chromatic_implies_OPG_hadwiger_fractional_chromatic_minor.
