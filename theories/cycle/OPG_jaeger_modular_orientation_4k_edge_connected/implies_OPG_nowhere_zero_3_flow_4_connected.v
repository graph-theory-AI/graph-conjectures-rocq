(** * Jaeger's modular orientation conjecture implies the 3-flow conjecture

For [k = 1], Jaeger's conjecture orients every 4-edge-connected graph so that the imbalance of
every vertex is a multiple of 3.  The values 1 along this orientation then form a nowhere-zero
Z_3-flow, which Tutte's theorem turns into a nowhere-zero 3-flow ([mod_flow_nowhere_zero]).

The implication is noted by Jaeger, "Nowhere-zero flow problems", Selected Topics in Graph
Theory 3 (1988) 71-95.  It was formalized in graph-theory-rocq
(cycle-theory/theories/conjectures/implications_D1.v). *)

From GraphTheory Require Import mgraph.
From mathcomp Require Import boot algebra.
From GC.GraphLib Require Import cycle flow.
From GC.cycle.OPG_jaeger_modular_orientation_4k_edge_connected Require Import
  main(OPG_jaeger_modular_orientation_4k_edge_connected).
From GC.cycle.OPG_nowhere_zero_3_flow_4_connected Require Import
  main(OPG_nowhere_zero_3_flow_4_connected).

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.

Theorem OPG_jaeger_modular_orientation_4k_edge_connected_implies_OPG_nowhere_zero_3_flow_4_connected :
  OPG_jaeger_modular_orientation_4k_edge_connected -> OPG_nowhere_zero_3_flow_4_connected.
Proof.
move=> J G E0 G4; have [o ho] := J 1%N G E0 isT G4.
apply: (@mod_flow_nowhere_zero _ 3 (fun e => if o e then 1 else -1)%R) => // [v|e].
  have [q hq] := ho v; have hq' : orient_imbalance o v = (3 * q)%R := hq.
  by rewrite mnet_orient hq' rpredN dvdz_mulr.
by case: (o e).
Qed.

Check (OPG_jaeger_modular_orientation_4k_edge_connected_implies_OPG_nowhere_zero_3_flow_4_connected :
  GC.cycle.OPG_jaeger_modular_orientation_4k_edge_connected.main.OPG_jaeger_modular_orientation_4k_edge_connected ->
  GC.cycle.OPG_nowhere_zero_3_flow_4_connected.main.OPG_nowhere_zero_3_flow_4_connected).
Print Assumptions OPG_jaeger_modular_orientation_4k_edge_connected_implies_OPG_nowhere_zero_3_flow_4_connected.
