(** * Reduction of the 5-cycle double cover conjecture to cubic graphs

If every bridgeless loopless cubic graph has a double cover by five even subgraphs, then so has
every bridgeless graph ([cubic_reduction]).

Inflate each vertex of a bridgeless graph [G] into a cycle ([inflate] of
GraphLib/cubic_inflation.v): the inflated graph is loopless, cubic and bridgeless, and contracting
the cycles maps its even subgraphs to even subgraphs of [G].  Hence a double cover of the inflated graph by five even
subgraphs gives one of [G].

The reduction is classical (Jaeger, "A survey of the cycle double cover conjecture", 1985).  This
proof comes from graph-theory-rocq (cycle-theory/theories/conjectures/implications_U6.v). *)

From GraphTheory Require Import mgraph.
From mathcomp Require Import boot.
From GC.GraphLib Require Import misc cycle even_subgraph cubic_inflation.
From GC.cycle.OPG_bridgeless_cycle_double_cover_5_cycles Require Import
  main(OPG_bridgeless_cycle_double_cover_5_cycles).

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** [G] has a double cover by five even subgraphs. *)
Definition five_cover (G : mgraph) : Prop :=
  exists L : seq {set edge G},
    [/\ size L = 5, (forall C, C \in L -> even_subgraph C)
      & forall e : edge G, count (fun C : {set edge G} => e \in C) L = 2].

(** Contracting the cycles of the inflation maps a double cover by five even subgraphs to one. *)
Lemma contract_cover (G : mgraph) : five_cover (inflate G) -> five_cover G.
Proof.
case=> L [Ls Le Ln]; exists (map (@contract G) L); split.
- by rewrite size_map.
- by move=> _ /mapP[C CL ->]; apply: contract_even; apply: Le.
- by move=> e; rewrite count_map -(Ln (inl e)); apply: eq_count => C; rewrite /= inE.
Qed.

Theorem cubic_reduction :
  (forall H : mgraph, 0 < #|H| -> loopless_cubic H -> bridgeless H -> five_cover H) ->
  OPG_bridgeless_cycle_double_cover_5_cycles.
Proof.
move=> h G _ /card_gt0P[e0 _] bl; apply: contract_cover; apply: h.
- by apply/card_gt0P; exists ((e0, false) : inflate G).
- by split; [exact: inflate_loopless | exact: inflate_cubic].
- exact: inflate_bridgeless.
Qed.
