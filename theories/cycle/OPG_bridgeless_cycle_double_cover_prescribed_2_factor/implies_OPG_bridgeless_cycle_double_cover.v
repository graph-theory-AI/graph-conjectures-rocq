(** * Cycle double covers containing a prescribed 2-regular subgraph imply the cycle double cover
      conjecture

With the empty 2-regular subgraph, the conjecture gives a cycle double cover of every 2-connected
loopless cubic graph.  The cycle double cover conjecture reduces to these graphs: it suffices to
cover a bridgeless graph [G] whose cuts separating two vertices have at least three edges
([cdc_small_cut_reduction]).  If [G] has a single edge, it is a loop, covered twice.  Otherwise,
inflate every vertex of [G] into a cycle: the inflated graph is loopless, cubic, bridgeless and
connected, hence 2-connected, with at least four vertices.  Contracting the cycles of its cycle
double cover gives even subgraphs of [G] covering every edge twice, which split into cycles.

The implication is mentioned in the Open Problem Garden, and is the relation e098 of
graph-conjectures.  It was formalized in graph-theory-rocq
(cycle-theory/theories/conjectures/implications_U6.v). *)

From GraphTheory Require Import mgraph.
From GraphTheory Require Import digraph sgraph connectivity.
From GraphTheory Require skeleton.
From mathcomp Require Import boot.
From GC.GraphLib Require Import misc cycle even_subgraph cubic_inflation.
From GC.cycle.OPG_eulerian_cycle_decomposition_compatible_transition_system Require Import
  small_cut_reduction(cdc_small_cut_reduction).
From GC.cycle.OPG_bridgeless_cycle_double_cover_prescribed_2_factor Require Import
  main(OPG_bridgeless_cycle_double_cover_prescribed_2_factor).
From GC.cycle.OPG_bridgeless_cycle_double_cover Require Import
  main(OPG_bridgeless_cycle_double_cover).

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** A loop is a cycle. *)
Lemma loop_circuit (G : mgraph) (e : edge G) : source e = target e -> is_circuit [set e].
Proof.
move=> st; split=> [|v|x y]; first by apply/set0Pn; exists e; rewrite inE.
  by rewrite mdeg_inE big_set1 -st; case: eqP; [right|left].
have end1 z : subgraph_incident [set e] z -> z = source e.
  by case/existsP => f /andP[]; rewrite inE => /eqP -> /existsP[[] /eqP <-].
by move=> /end1 -> /end1 ->; exists [::]; rewrite /uwalk_in /= eqxx.
Qed.

Theorem OPG_bridgeless_cycle_double_cover_prescribed_2_factor_implies_OPG_bridgeless_cycle_double_cover :
  OPG_bridgeless_cycle_double_cover_prescribed_2_factor -> OPG_bridgeless_cycle_double_cover.
Proof.
move=> A G _ E0 bl; apply: cdc_small_cut_reduction E0 bl => {}G E0 bl cut3.
have con : forall x y : G, exists w, uwalk x y w.
  by apply: mcut_uwalk => S x y xS yS; rewrite -card_gt0 (ltn_trans _ (cut3 S x y xS yS)).
have [E1|E2] := leqP #|edge G| 1.
  (* a single edge [e], which is a loop since the cut around [source e] has three edges *)
  case/card_gt0P: E0 => e _; have one f : f = e by apply: (card_le1_eqP E1).
  have st : source e = target e.
    apply/eqP; apply/negPn/negP => ne.
    have := cut3 [set source e] (source e) (target e) (set11 _); rewrite inE eq_sym => /(_ ne).
    by move/leq_trans/(_ (leq_trans (max_card _) E1)).
  exists [:: [set e]; [set e]]; split => [C|f]; last by rewrite (one f) /= !inE eqxx.
  by rewrite !inE => /orP[] /eqP ->; apply: loop_circuit.
(* the inflated graph [H], whose separating cuts have at least two edges *)
pose H := inflate G; have ll := inflate_loopless bl; have cub := inflate_cubic bl.
have cutH (S : {set H}) a b : a \in S -> b \notin S -> 1 < #|mcut S|.
  move=> aS bS; have [W hW] := inflate_uwalk con a b.
  have [|e _ eS] := uwalk_mcut (S := S) hW; first by rewrite aS bS.
  exact: bridgeless_mcut (inflate_bridgeless bl) eS.
have [|||||L [[Lc Ln] _]] := A H set0 _ _ _ _ _.
- by rewrite card_prod card_bool muln_gt0 E0.
- by split.
- apply: cubic_2connected ll cub cutH _.
  by rewrite card_prod card_bool (@leq_trans (2 * 2)) // leq_mul2r E2 orbT.
- by change (subgraph_kregular (set0 : {set edge H}) 2) => v; left; rewrite mdeg_inE big_set0.
- apply: (@mcut_connected (remove_edges (set0 : {set edge H}))) => S a b aS bS.
  have /card_gt0P[e eS] : 0 < #|@mcut H S| by apply: ltnW (cutH S a b aS bS).
  by apply/set0Pn; exists (Sub e (negbT (in_set0 e))); rewrite inE; rewrite inE in eS.
(* contract the cycles of the cycle double cover of [H] *)
have [|M [Mc Mn]] := @even_subgraphs_cycles G (map (@contract G) L).
  move=> _ /mapP[C CL ->]; apply: contract_even => v.
  by have [_ reg _] : is_circuit C := Lc C CL; case: (reg v) => ->.
exists M; split => // e; rewrite Mn count_map -(Ln (inl e)).
by apply: eq_count => C; rewrite /= inE.
Qed.

Check (OPG_bridgeless_cycle_double_cover_prescribed_2_factor_implies_OPG_bridgeless_cycle_double_cover :
  GC.cycle.OPG_bridgeless_cycle_double_cover_prescribed_2_factor.main.OPG_bridgeless_cycle_double_cover_prescribed_2_factor ->
  GC.cycle.OPG_bridgeless_cycle_double_cover.main.OPG_bridgeless_cycle_double_cover).
Print Assumptions
  OPG_bridgeless_cycle_double_cover_prescribed_2_factor_implies_OPG_bridgeless_cycle_double_cover.
