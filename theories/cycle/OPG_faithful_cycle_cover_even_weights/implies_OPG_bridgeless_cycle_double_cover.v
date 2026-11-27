(** * The faithful cycle cover conjecture implies the cycle double cover conjecture

A cycle double cover is a faithful cycle cover for the constant weight 2.  This weight is even, and
it is admissible for a bridgeless graph: the weight of a cut is twice its number of edges, hence
even, and at least 4 = 2 * 2 when the cut is nonempty, since a cut with a single edge would make
this edge a bridge.

This is the observation of Seymour, who stated the faithful cover conjecture as a generalization of
the cycle double cover conjecture.  It was formalized in graph-theory-rocq
(cycle-theory/theories/conjectures/implications_U6.v). *)

From GraphTheory Require Import mgraph.
From mathcomp Require Import boot.
From GC.GraphLib Require Import misc(bridgeless_mcut).
From GC.cycle.OPG_faithful_cycle_cover_even_weights Require Import
  main(OPG_faithful_cycle_cover_even_weights).
From GC.cycle.OPG_bridgeless_cycle_double_cover Require Import
  main(OPG_bridgeless_cycle_double_cover).

Theorem OPG_faithful_cycle_cover_even_weights_implies_OPG_bridgeless_cycle_double_cover :
  OPG_faithful_cycle_cover_even_weights -> OPG_bridgeless_cycle_double_cover.
Proof.
move=> FC G G0 E0 bl; apply: (FC G (fun=> 2)) => // S e eS.
by rewrite sum_nat_const oddM andbF leq_mul2r /=; split => //; apply: bridgeless_mcut eS.
Qed.

Check (OPG_faithful_cycle_cover_even_weights_implies_OPG_bridgeless_cycle_double_cover :
  GC.cycle.OPG_faithful_cycle_cover_even_weights.main.OPG_faithful_cycle_cover_even_weights ->
  GC.cycle.OPG_bridgeless_cycle_double_cover.main.OPG_bridgeless_cycle_double_cover).
Print Assumptions
  OPG_faithful_cycle_cover_even_weights_implies_OPG_bridgeless_cycle_double_cover.
