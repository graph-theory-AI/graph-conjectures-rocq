(** * The 5-cycle double cover conjecture implies the cycle double cover conjecture

A double cover of a bridgeless graph by five even subgraphs gives a cycle double cover: by Veblen's
theorem, each even subgraph is partitioned by cycles, and the list of all these cycles covers each
edge twice.

The implication is the edge e084 of relations.json in graph-conjectures.  It was formalized in
graph-theory-rocq (cycle-theory/theories/conjectures/implications_U6.v). *)

From GraphTheory Require Import mgraph.
From mathcomp Require Import boot.
From GC.GraphLib Require Import even_subgraph.
From GC.cycle.OPG_bridgeless_cycle_double_cover_5_cycles Require Import
  main(OPG_bridgeless_cycle_double_cover_5_cycles).
From GC.cycle.OPG_bridgeless_cycle_double_cover Require Import
  main(OPG_bridgeless_cycle_double_cover).

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Theorem OPG_bridgeless_cycle_double_cover_5_cycles_implies_OPG_bridgeless_cycle_double_cover :
  OPG_bridgeless_cycle_double_cover_5_cycles -> OPG_bridgeless_cycle_double_cover.
Proof.
move=> cover5 G G0 E0 bl; have [L [_ Le Ln]] := cover5 G G0 E0 bl.
have [M [Mc Mn]] := even_subgraphs_cycles Le.
by exists M; split => // e; rewrite Mn Ln.
Qed.

Check (OPG_bridgeless_cycle_double_cover_5_cycles_implies_OPG_bridgeless_cycle_double_cover :
  GC.cycle.OPG_bridgeless_cycle_double_cover_5_cycles.main.OPG_bridgeless_cycle_double_cover_5_cycles ->
  GC.cycle.OPG_bridgeless_cycle_double_cover.main.OPG_bridgeless_cycle_double_cover).

Print Assumptions OPG_bridgeless_cycle_double_cover_5_cycles_implies_OPG_bridgeless_cycle_double_cover.
