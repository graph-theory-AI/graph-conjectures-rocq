(** * Jaeger's modular orientation conjecture implies the 5-flow conjecture

Jaeger's conjecture is used for [k = 2] only.  By [nowhere_zero_flow_reduction], it suffices to
find a nowhere-zero 5-flow in a graph [G] whose cuts separating two vertices have at least 3
edges.  The graph [3G], with every edge tripled, is then 9-edge-connected, so Jaeger's conjecture
orients it with imbalances multiple of 5.  Summing the values 1 along this orientation over the
three copies of each edge gives values in {±1, ±3}, never multiple of 5, with net outflows
multiple of 5: a nowhere-zero Z_5-flow of [G], which Tutte's theorem turns into a nowhere-zero
5-flow ([mod_flow_nowhere_zero]).

The implication is the edge e167 of relations.json in graph-conjectures.  It was formalized in
graph-theory-rocq (cycle-theory/theories/conjectures/implications_D1.v). *)

From GraphTheory Require Import mgraph.
From mathcomp Require Import boot algebra.
From GC.GraphLib Require Import misc cycle flow.
From GC.cycle.OPG_jaeger_modular_orientation_4k_edge_connected Require Import
  main(OPG_jaeger_modular_orientation_4k_edge_connected).
From GC.cycle.OPG_nowhere_zero_5_flow_bridgeless Require Import
  main(OPG_nowhere_zero_5_flow_bridgeless).

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.

Theorem OPG_jaeger_modular_orientation_4k_edge_connected_implies_OPG_nowhere_zero_5_flow_bridgeless :
  OPG_jaeger_modular_orientation_4k_edge_connected -> OPG_nowhere_zero_5_flow_bridgeless.
Proof.
move=> J; apply: nowhere_zero_flow_reduction => G E0 cut3.
have G9 : medge_connected (medge_mult G 3) (4 * 2).
  apply: mcut_medge_connected => S x y xS yS; rewrite medge_mult_mcut.
  by apply: (@leq_trans (3 * 3)); rewrite // leq_mul2r (cut3 S x y).
have E3 : 0 < #|edge (medge_mult G 3)| by rewrite card_prod card_ord muln_gt0 E0.
have [o ho] := J 2 _ E3 isT G9.
apply: (@mod_flow_nowhere_zero _ 5
  (fun e => \sum_(i < 3) if o (e, i) then 1 else -1)%R) => // [v|e].
  have [q hq] := ho v; have hq' : orient_imbalance o v = (5 * q)%R := hq.
  by rewrite (medge_mult_mnet (fun f => if o f then 1 else -1)%R) mnet_orient hq' rpredN dvdz_mulr.
by rewrite !big_ord_recl big_ord0; case: (o (e, _)); case: (o (e, _)); case: (o (e, _)).
Qed.

Check (OPG_jaeger_modular_orientation_4k_edge_connected_implies_OPG_nowhere_zero_5_flow_bridgeless :
  GC.cycle.OPG_jaeger_modular_orientation_4k_edge_connected.main.OPG_jaeger_modular_orientation_4k_edge_connected ->
  GC.cycle.OPG_nowhere_zero_5_flow_bridgeless.main.OPG_nowhere_zero_5_flow_bridgeless).
Print Assumptions OPG_jaeger_modular_orientation_4k_edge_connected_implies_OPG_nowhere_zero_5_flow_bridgeless.
