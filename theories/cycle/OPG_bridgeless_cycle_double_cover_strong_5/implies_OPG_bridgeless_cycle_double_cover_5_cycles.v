(** * The strong 5-cycle double cover conjecture implies the 5-cycle double cover conjecture

The strong conjecture gives a double cover by five even subgraphs of every bridgeless loopless
cubic graph: such a graph has a cycle, since its edges form a nonempty set without vertex of degree
one, and the condition that one member contains this cycle is forgotten.  The 5-cycle double cover
conjecture follows by the classical reduction to cubic graphs ([cubic_reduction]).

The implication is the edge e085 of relations.json in graph-conjectures.  It was formalized in
graph-theory-rocq (cycle-theory/theories/conjectures/implications_U6.v). *)

From GraphTheory Require Import mgraph.
From mathcomp Require Import boot.
From GC.GraphLib Require Import misc even_subgraph.
From GC.cycle.OPG_bridgeless_cycle_double_cover_5_cycles Require Import cubic_reduction.
From GC.cycle.OPG_bridgeless_cycle_double_cover_strong_5 Require Import
  main(OPG_bridgeless_cycle_double_cover_strong_5).
From GC.cycle.OPG_bridgeless_cycle_double_cover_5_cycles Require Import
  main(OPG_bridgeless_cycle_double_cover_5_cycles).

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Theorem OPG_bridgeless_cycle_double_cover_strong_5_implies_OPG_bridgeless_cycle_double_cover_5_cycles :
  OPG_bridgeless_cycle_double_cover_strong_5 -> OPG_bridgeless_cycle_double_cover_5_cycles.
Proof.
move=> strong; apply: cubic_reduction => H H0 [ll cub] bl; have /card_gt0P[v _] := H0.
have deg u : mdeg_in [set: edge H] u = 3 by rewrite mdeg_in_loopless // setTI cub.
have [C _ Cc] : exists2 C : {set edge H}, C \subset setT & is_circuit C.
  apply: has_circuit => [|u]; last by rewrite deg.
  have /card_gt0P[e _] : 0 < #|edges_at v| by rewrite cub.
  by apply/set0Pn; exists e; rewrite inE.
have [L [L5 Le Ln _]] := strong H C H0 (conj ll cub) bl Cc.
by exists L.
Qed.

Check (OPG_bridgeless_cycle_double_cover_strong_5_implies_OPG_bridgeless_cycle_double_cover_5_cycles :
  GC.cycle.OPG_bridgeless_cycle_double_cover_strong_5.main.OPG_bridgeless_cycle_double_cover_strong_5 ->
  GC.cycle.OPG_bridgeless_cycle_double_cover_5_cycles.main.OPG_bridgeless_cycle_double_cover_5_cycles).

Print Assumptions
  OPG_bridgeless_cycle_double_cover_strong_5_implies_OPG_bridgeless_cycle_double_cover_5_cycles.
