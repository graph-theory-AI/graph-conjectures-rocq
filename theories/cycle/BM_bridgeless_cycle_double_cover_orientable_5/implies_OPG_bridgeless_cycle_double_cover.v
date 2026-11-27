(** * The orientable 5-cycle double cover conjecture implies the cycle double cover conjecture

Composition of two implications: the orientable 5-cycle double cover conjecture implies the 5-cycle
double cover conjecture (by forgetting the orientations and identifying a vertex of each component
of a disconnected graph), which implies the cycle double cover conjecture (by Veblen's theorem).

The implication is the edge e218 of relations.json in graph-conjectures.  It was formalized in
graph-theory-rocq (cycle-theory/theories/conjectures/implications_U6.v). *)

From GC.cycle.BM_bridgeless_cycle_double_cover_orientable_5 Require Import
  implies_OPG_bridgeless_cycle_double_cover_5_cycles(
    BM_bridgeless_cycle_double_cover_orientable_5_implies_OPG_bridgeless_cycle_double_cover_5_cycles).
From GC.cycle.OPG_bridgeless_cycle_double_cover_5_cycles Require Import
  implies_OPG_bridgeless_cycle_double_cover(
    OPG_bridgeless_cycle_double_cover_5_cycles_implies_OPG_bridgeless_cycle_double_cover).
From GC.cycle.BM_bridgeless_cycle_double_cover_orientable_5 Require Import
  main(BM_bridgeless_cycle_double_cover_orientable_5).
From GC.cycle.OPG_bridgeless_cycle_double_cover Require Import
  main(OPG_bridgeless_cycle_double_cover).

Theorem BM_bridgeless_cycle_double_cover_orientable_5_implies_OPG_bridgeless_cycle_double_cover :
  BM_bridgeless_cycle_double_cover_orientable_5 -> OPG_bridgeless_cycle_double_cover.
Proof.
intro orientable.
apply OPG_bridgeless_cycle_double_cover_5_cycles_implies_OPG_bridgeless_cycle_double_cover.
apply BM_bridgeless_cycle_double_cover_orientable_5_implies_OPG_bridgeless_cycle_double_cover_5_cycles.
exact orientable.
Qed.

Check (BM_bridgeless_cycle_double_cover_orientable_5_implies_OPG_bridgeless_cycle_double_cover :
  GC.cycle.BM_bridgeless_cycle_double_cover_orientable_5.main.BM_bridgeless_cycle_double_cover_orientable_5 ->
  GC.cycle.OPG_bridgeless_cycle_double_cover.main.OPG_bridgeless_cycle_double_cover).

Print Assumptions
  BM_bridgeless_cycle_double_cover_orientable_5_implies_OPG_bridgeless_cycle_double_cover.
