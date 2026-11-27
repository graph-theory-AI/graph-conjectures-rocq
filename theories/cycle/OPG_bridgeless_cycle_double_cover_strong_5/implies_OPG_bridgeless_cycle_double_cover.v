(** * The strong 5-cycle double cover conjecture implies the cycle double cover conjecture

Composition of two implications: the strong 5-cycle double cover conjecture implies the 5-cycle
double cover conjecture (by the reduction to cubic graphs), which implies the cycle double cover
conjecture (by Veblen's theorem).

The implication is the edge e086 of relations.json in graph-conjectures.  It was formalized in
graph-theory-rocq (cycle-theory/theories/conjectures/implications_U6.v). *)

From GC.cycle.OPG_bridgeless_cycle_double_cover_strong_5 Require Import
  implies_OPG_bridgeless_cycle_double_cover_5_cycles(
    OPG_bridgeless_cycle_double_cover_strong_5_implies_OPG_bridgeless_cycle_double_cover_5_cycles).
From GC.cycle.OPG_bridgeless_cycle_double_cover_5_cycles Require Import
  implies_OPG_bridgeless_cycle_double_cover(
    OPG_bridgeless_cycle_double_cover_5_cycles_implies_OPG_bridgeless_cycle_double_cover).
From GC.cycle.OPG_bridgeless_cycle_double_cover_strong_5 Require Import
  main(OPG_bridgeless_cycle_double_cover_strong_5).
From GC.cycle.OPG_bridgeless_cycle_double_cover Require Import
  main(OPG_bridgeless_cycle_double_cover).

Theorem OPG_bridgeless_cycle_double_cover_strong_5_implies_OPG_bridgeless_cycle_double_cover :
  OPG_bridgeless_cycle_double_cover_strong_5 -> OPG_bridgeless_cycle_double_cover.
Proof.
intro strong.
apply OPG_bridgeless_cycle_double_cover_5_cycles_implies_OPG_bridgeless_cycle_double_cover.
apply OPG_bridgeless_cycle_double_cover_strong_5_implies_OPG_bridgeless_cycle_double_cover_5_cycles.
exact strong.
Qed.

Check (OPG_bridgeless_cycle_double_cover_strong_5_implies_OPG_bridgeless_cycle_double_cover :
  GC.cycle.OPG_bridgeless_cycle_double_cover_strong_5.main.OPG_bridgeless_cycle_double_cover_strong_5 ->
  GC.cycle.OPG_bridgeless_cycle_double_cover.main.OPG_bridgeless_cycle_double_cover).

Print Assumptions OPG_bridgeless_cycle_double_cover_strong_5_implies_OPG_bridgeless_cycle_double_cover.
