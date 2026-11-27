(** * Compatible decompositions of eulerian graphs imply the cycle double cover conjecture

Let G be a bridgeless graph.

- If every cut separating two vertices of G has at least 3 edges, double every edge of G.  The
  doubled graph is eulerian and 6-edge-connected.  Pair the two copies of each edge at each vertex:
  this is a transition system, and a compatible decomposition of the doubled graph never contains
  the two copies of an edge in the same cycle (at an end of a non-loop, they would form a pair of
  the transition system; a loop would give degree 4).  The images of its cycles in G form a cycle
  double cover of G.
- The general case reduces to this one ([cdc_small_cut_reduction] in small_cut_reduction.v): a
  cut of 0 or 2 edges separating two vertices is removed by identifying two vertices on both sides
  of the cut, and even double covers lift back.

The implication is mentioned in the Open Problem Garden, and is the relation e187 of
graph-conjectures.  It was formalized in graph-theory-rocq
(cycle-theory/theories/conjectures/implications_D1.v). *)

From GraphTheory Require Import mgraph.
From mathcomp Require Import boot.
From GC.GraphLib Require Import misc cycle.
From GC.cycle.OPG_eulerian_cycle_decomposition_compatible_transition_system Require Import
  small_cut_reduction.
From GC.cycle.OPG_eulerian_cycle_decomposition_compatible_transition_system Require Import
  main(OPG_eulerian_cycle_decomposition_compatible_transition_system).
From GC.cycle.OPG_bridgeless_cycle_double_cover Require Import
  main(OPG_bridgeless_cycle_double_cover).

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Doubling the edges *)

Section Doubling.
Variable G : mgraph.

Definition dbl : mgraph :=
  @Graph unit unit G (edge G * bool)%type (fun b f => endpoint b f.1) (fun _ => tt) (fun _ => tt).

Lemma dbl_mcut (S : {set G}) : #|@mcut dbl S| = 2 * #|mcut S|.
Proof.
have -> : @mcut dbl S = setX (mcut S) [set: bool].
  by apply/setP => -[e i]; rewrite !inE andbT.
by rewrite cardsX cardsT card_bool mulnC.
Qed.

Lemma dbl_mdeg (v : G) : @mdeg dbl v = 2 * mdeg v.
Proof.
have h b : [set f in [set: edge dbl] | endpoint b f == v]
           = setX [set e in [set: edge G] | endpoint b e == v] [set: bool].
  by apply/setP => -[e i]; rewrite !inE /= andbT.
by rewrite /mdeg /mdeg_in !h !cardsX cardsT card_bool mulnDr !(mulnC 2).
Qed.

(** The transition system pairing the two copies of each edge. *)
Definition dblP (v : dbl) : {set {set edge dbl}} :=
  [set [set (g, false); (g, true)] | g in edges_at (v : G)].

Lemma dblP_system : transition_system dblP.
Proof.
split=> [v|v T]; last by case/imsetP => g _ ->; rewrite cards2 xpair_eqE eqxx.
have dis : {in edges_at (v : G) &, forall i j, j != i ->
    [disjoint [set (i, false); (i, true)] & [set ((j, false) : edge dbl); (j, true)]]}.
  move=> i j _ _ ji; rewrite -setI_eq0; apply/eqP/setP => -[g b]; rewrite !inE !xpair_eqE.
  by case: (g =P i) => [->|] //=; rewrite [i == j]eq_sym (negbTE ji) /= andbF.
have P0 : set0 \notin dblP v by apply/imsetP => -[g _ /setP/(_ (g, false))]; rewrite !inE eqxx.
have [tI _] := trivIimset dis P0.
apply/and3P; split => //; apply/eqP/setP => -[g b]; apply/bigcupP/idP => [[T]|gv].
  by case/imsetP => g' g'v -> /set2P[] [-> _]; rewrite inE; rewrite inE in g'v.
exists [set (g, false); (g, true)]; last by case: b {gv}; rewrite !inE eqxx ?orbT.
by apply/imsetP; exists g; rewrite // inE; rewrite inE in gv.
Qed.

(** The edges of [G] with a copy in [C]. *)
Definition dbl_proj (C : {set edge dbl}) : {set edge G} :=
  [set g | ((g, false) \in C) || ((g, true) \in C)].

Definition one_copy (C : {set edge dbl}) := forall g, ~~ (((g, false) \in C) && ((g, true) \in C)).

(** A compatible cycle holds at most one copy of each edge. *)
Lemma compatible_one_copy (C : {set edge dbl}) :
  is_circuit C -> (forall v, (edges_at v :&: C) \notin dblP v) -> one_copy C.
Proof.
move=> [_ reg _] comp g; apply/negP => /andP[g0 g1].
pose v : dbl := source g; pose T : {set edge dbl} := [set (g, false); (g, true)].
have Ts b : endpoint b g = v -> T \subset [set f in C | endpoint b f == v].
  by move=> bv; apply/subsetP => f /set2P[] ->; rewrite !inE /= bv eqxx ?g0 ?g1.
have T2 : #|T| = 2 by rewrite cards2 xpair_eqE eqxx.
have s2 := subset_leq_card (Ts false erefl); rewrite T2 in s2.
have := reg v; rewrite /mdeg_in; have [tv|tv] := eqVneq (target g) v.
  have t2 := subset_leq_card (Ts true tv); rewrite T2 in t2.
  by case=> d; have := leq_add s2 t2; rewrite d.
case=> d; first by have := leq_trans s2 (leq_addr #|[set f in C | target f == v]| _); rewrite d.
have /cards0_eq t0 : #|[set f in C | target f == v]| = 0.
  by apply/eqP; rewrite -leqn0 -(leq_add2l #|[set f in C | source f == v]|) d addn0.
have sT : [set f in C | source f == v] = T.
  by apply/eqP; rewrite eq_sym eqEcard Ts // T2 -d leq_addr.
apply: (negP (comp v)); suff -> : edges_at v :&: C = T.
  by apply/imsetP; exists g; rewrite // !inE; apply/existsP; exists false.
rewrite -sT; apply/setP => f; move/setP/(_ f): t0; rewrite !inE.
case: (f \in C) => /= [/negbT tf|_]; rewrite ?andbT ?andbF //.
by apply/existsP/idP => [[[] fb] //|sf]; [rewrite fb in tf | exists false].
Qed.

Lemma dbl_proj_ends (C : {set edge dbl}) b v : one_copy C ->
  #|[set g in dbl_proj C | endpoint b g == v]| = #|[set f in C | endpoint b f == v]|.
Proof.
pose fst (f : edge dbl) := f.1.
move=> oc; have inj : {in [set f in C | endpoint b f == v] &, injective fst}.
  move=> [g1 b1] [g2 b2]; rewrite !inE /= => /andP[h1 _] /andP[h2 _] e12; subst g2.
  by move: (oc g1) h1 h2; case: b1; case: b2 => // /negP + h1 h2; rewrite h1 h2.
rewrite -(card_in_imset inj); apply: eq_card => g; rewrite !inE.
apply/andP/imsetP => [[/orP[] gC gv]|[[g' b'] /[!inE] /andP[gC gv] ->]].
- by exists (g, false); rewrite // !inE gC.
- by exists (g, true); rewrite // !inE gC.
by split=> //; case: b' gC {gv} => /= ->; rewrite ?orbT.
Qed.

Lemma dbl_uwalk x y (w : seq (edge dbl)) : uwalk x y w -> @uwalk G x y (map (fun f => f.1) w).
Proof. by elim: w x => [|f w IH] x //= /orP[]/andP[-> /IH ->]; rewrite ?orbT. Qed.

(** The edges of a cycle with one copy of each edge form a cycle of [G]. *)
Lemma dbl_proj_circuit (C : {set edge dbl}) :
  is_circuit C -> one_copy C -> is_circuit (dbl_proj C).
Proof.
move=> [C0 reg con] oc; split.
- case/set0Pn: C0 => -[g b] gC; apply/set0Pn; exists g; rewrite inE.
  by case: b gC => ->; rewrite ?orbT.
- by move=> v; rewrite /mdeg_in !dbl_proj_ends //; exact: reg.
move=> x y hx hy.
have inc z : subgraph_incident (dbl_proj C) z -> subgraph_incident C (z : dbl).
  case/existsP => g /andP[]; rewrite inE => /orP[] gC gz; apply/existsP.
  - by exists (g, false); rewrite gC.
  - by exists (g, true); rewrite gC.
have [w /andP[wu wC]] := con _ _ (inc _ hx) (inc _ hy).
exists (map (fun f => f.1) w); rewrite /uwalk_in dbl_uwalk //=.
apply/allP => g /mapP[[g' b] gw ->].
by rewrite inE; case: b gw => /(allP wC) ->; rewrite ?orbT.
Qed.

(** The images of the cycles of a compatible decomposition of [dbl] form a cycle double cover of
    [G]. *)
Lemma dbl_cdc D : compatible_decomposition dblP D -> cycle_double_cover (map dbl_proj D).
Proof.
move=> [[Dc Dn] comp]; have oc C : C \in D -> one_copy C.
  by move=> CD; apply: compatible_one_copy (Dc C CD) (comp C CD).
split=> [C' /mapP[C CD ->]|g]; first exact: dbl_proj_circuit (Dc C CD) (oc C CD).
have := count_predUI (fun C : {set edge dbl} => (g, false) \in C) (fun C => (g, true) \in C) D.
rewrite (Dn (g, false)) (Dn (g, true)) count_map; set m := count (predI _ _) D.
have -> : m = 0 by apply/eqP; rewrite -leqn0 leqNgt -has_count; apply/hasPn => C /oc /(_ g).
rewrite addn0 => e; rewrite [RHS](_ : 2 = 1 + 1) // -e.
by apply: eq_count => C; rewrite /= inE.
Qed.

End Doubling.

(** The case where every cut separating two vertices has at least three edges. *)
Lemma cdc_3_edge_connected :
  OPG_eulerian_cycle_decomposition_compatible_transition_system ->
  forall G : mgraph, 0 < #|edge G| -> bridgeless G ->
    (forall (S : {set G}) x y, x \in S -> y \notin S -> 2 < #|mcut S|) ->
  exists L : seq {set edge G}, cycle_double_cover L.
Proof.
move=> A G E0 _ cut3.
have cut6 (S : {set G}) x y : x \in S -> y \notin S -> 5 < #|@mcut (dbl G) S|.
  by move=> xS yS; rewrite dbl_mcut (@leq_trans (2 * 3)) // leq_mul2l (cut3 S x y).
have [|||D hD] :=
  A (dbl G) (@dblP G) _ _ (@mcut_medge_connected (dbl G) 6 cut6) _ (dblP_system G).
- by move: E0 => /card_gt0P[e _]; apply/card_gt0P; exists (source e); rewrite inE.
- by rewrite card_prod muln_gt0 E0 card_bool.
- split=> [|v]; last by change (~~ odd (@mdeg (dbl G) v)); rewrite dbl_mdeg oddM.
  apply: (@mcut_connected (dbl G)) => S x y xS yS.
  by rewrite -card_gt0 (leq_trans _ (cut6 S x y xS yS)).
by exists (map (@dbl_proj G) D); exact: dbl_cdc.
Qed.

Theorem OPG_eulerian_cycle_decomposition_compatible_transition_system_implies_OPG_bridgeless_cycle_double_cover :
  OPG_eulerian_cycle_decomposition_compatible_transition_system ->
  OPG_bridgeless_cycle_double_cover.
Proof.
by move=> A G _ E0 bl; apply: cdc_small_cut_reduction (cdc_3_edge_connected A) _ E0 bl.
Qed.

Check (OPG_eulerian_cycle_decomposition_compatible_transition_system_implies_OPG_bridgeless_cycle_double_cover :
  GC.cycle.OPG_eulerian_cycle_decomposition_compatible_transition_system.main.OPG_eulerian_cycle_decomposition_compatible_transition_system ->
  GC.cycle.OPG_bridgeless_cycle_double_cover.main.OPG_bridgeless_cycle_double_cover).
Print Assumptions
  OPG_eulerian_cycle_decomposition_compatible_transition_system_implies_OPG_bridgeless_cycle_double_cover.
