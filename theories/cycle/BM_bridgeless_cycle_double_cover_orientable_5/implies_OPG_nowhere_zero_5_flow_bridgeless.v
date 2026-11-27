(** * The orientable five cycle double cover conjecture implies the 5-flow conjecture

An orientable double cover by five even subgraphs [C 0, ..., C 4], with balanced orientations
[d i], gives the flow [sum_i i s_i], where [s_i] is the flow with values ±1 along [d i] on [C i]
and 0 elsewhere.  Every edge lies in exactly two of the subgraphs, [C i] and [C j], in opposite
directions: its value is [±(i - j)], between 1 and 4 in absolute value.  The conjecture is about
2-edge-connected graphs, and [nowhere_zero_flow_reduction] reduces the 5-flow conjecture to graphs
whose cuts separating two vertices have at least 3 edges.

The implication is the edge e246 of relations.json in graph-conjectures.  It was formalized in
graph-theory-rocq (cycle-theory/theories/conjectures/implications_D1.v). *)

From GraphTheory Require Import mgraph.
From mathcomp Require Import boot order algebra.
From GC.GraphLib Require Import misc cycle flow.
From GC.cycle.BM_bridgeless_cycle_double_cover_orientable_5 Require Import
  main(BM_bridgeless_cycle_double_cover_orientable_5).
From GC.cycle.OPG_nowhere_zero_5_flow_bridgeless Require Import
  main(OPG_nowhere_zero_5_flow_bridgeless).

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Num.Theory Order.TTheory.

Local Open Scope ring_scope.

Theorem BM_bridgeless_cycle_double_cover_orientable_5_implies_OPG_nowhere_zero_5_flow_bridgeless :
  BM_bridgeless_cycle_double_cover_orientable_5 -> OPG_nowhere_zero_5_flow_bridgeless.
Proof.
move=> HB; apply: nowhere_zero_flow_reduction => G E0 cut3.
have G0 : (0 < #|G|)%N by case/card_gt0P: E0 => e _; apply/card_gt0P; exists (source e).
have G2 : medge_connected G 2.
  by apply: mcut_medge_connected => S x y xS yS; apply: leq_trans (cut3 S x y xS yS).
have [C [d [_ bal two opp]]] := HB G G0 G2.
exists (fun e => \sum_(i < 5) (i : nat)%:R * osgn (C i) (d i) e); split.
  apply/conservativeE => v; rewrite mnet_sum big1 // => i _.
  by rewrite mnetZ; move/conservativeE: (osgn_conservative (bal i)) => ->; rewrite mulr0.
move=> e; have /cards2P[i [j [ij Cij]]] : #|[set i | e \in C i]| == 2%N by rewrite two.
have Ci : e \in C i by have := set21 i j; rewrite -Cij inE.
have Cj : e \in C j by have := set22 i j; rewrite -Cij inE.
rewrite (bigD1 i) // (bigD1 j) 1?eq_sym //= big1 ?addr0 => [k /andP[ki kj]|]; last first.
  have := opp e i j ij Ci Cj; rewrite /osgn Ci Cj.
  by move: i j ij {Ci Cj Cij}; do 2 case=> [[|[|[|[|[|//]]]]] ?] => //=;
    case: (d _ e); case: (d _ e).
rewrite /osgn; case: ifP => kC; rewrite ?mulr0 //.
have : k \in [set i | e \in C i] by rewrite inE.
by rewrite Cij !inE (negbTE ki) (negbTE kj).
Qed.

Check (BM_bridgeless_cycle_double_cover_orientable_5_implies_OPG_nowhere_zero_5_flow_bridgeless :
  GC.cycle.BM_bridgeless_cycle_double_cover_orientable_5.main.BM_bridgeless_cycle_double_cover_orientable_5 ->
  GC.cycle.OPG_nowhere_zero_5_flow_bridgeless.main.OPG_nowhere_zero_5_flow_bridgeless).
Print Assumptions BM_bridgeless_cycle_double_cover_orientable_5_implies_OPG_nowhere_zero_5_flow_bridgeless.
