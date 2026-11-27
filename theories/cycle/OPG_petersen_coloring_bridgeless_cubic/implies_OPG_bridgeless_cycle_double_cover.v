(** * The Petersen colouring conjecture implies the cycle double cover conjecture

Composition of two implications: the Petersen colouring conjecture implies the 5-cycle double
cover conjecture (by pulling back a double cover of the Petersen graph by five even subgraphs),
which implies the cycle double cover conjecture (by Veblen's theorem).

The implication is the edge e091 of relations.json in graph-conjectures.  It was formalized in
graph-theory-rocq (cycle-theory/theories/conjectures/implications_U6.v). *)

From GC.cycle.OPG_petersen_coloring_bridgeless_cubic Require Import
  implies_OPG_bridgeless_cycle_double_cover_5_cycles(
    OPG_petersen_coloring_bridgeless_cubic_implies_OPG_bridgeless_cycle_double_cover_5_cycles).
From GC.cycle.OPG_bridgeless_cycle_double_cover_5_cycles Require Import
  implies_OPG_bridgeless_cycle_double_cover(
    OPG_bridgeless_cycle_double_cover_5_cycles_implies_OPG_bridgeless_cycle_double_cover).
From GC.cycle.OPG_petersen_coloring_bridgeless_cubic Require Import
  main(OPG_petersen_coloring_bridgeless_cubic).
From GC.cycle.OPG_bridgeless_cycle_double_cover Require Import
  main(OPG_bridgeless_cycle_double_cover).

Theorem OPG_petersen_coloring_bridgeless_cubic_implies_OPG_bridgeless_cycle_double_cover :
  OPG_petersen_coloring_bridgeless_cubic -> OPG_bridgeless_cycle_double_cover.
Proof.
intro coloring.
apply OPG_bridgeless_cycle_double_cover_5_cycles_implies_OPG_bridgeless_cycle_double_cover.
apply OPG_petersen_coloring_bridgeless_cubic_implies_OPG_bridgeless_cycle_double_cover_5_cycles.
exact coloring.
Qed.

Check (OPG_petersen_coloring_bridgeless_cubic_implies_OPG_bridgeless_cycle_double_cover :
  GC.cycle.OPG_petersen_coloring_bridgeless_cubic.main.OPG_petersen_coloring_bridgeless_cubic ->
  GC.cycle.OPG_bridgeless_cycle_double_cover.main.OPG_bridgeless_cycle_double_cover).

Print Assumptions OPG_petersen_coloring_bridgeless_cubic_implies_OPG_bridgeless_cycle_double_cover.
