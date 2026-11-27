(** * The circular flow conjecture for odd r-graphs implies it for regular class 1 graphs

Let [G] be a loopless [(2t+1)]-regular graph of class 1.  Its [2t+1] colour classes are perfect
matchings, and a perfect matching meets every odd cut in an odd number of edges; the colour
classes being disjoint, every odd cut has at least [2t+1] edges, and [G] is a [(2t+1)]-graph.
This proves the implication for [t > 1].  For [t = 1] (not covered by the hypothesis), the
complements [A] and [B] of two colour classes are even subgraphs; balanced orientations of them
([even_balanced_orientation]) give flows [hA] and [hB] with values ±1 on them ([osgn]), and
[hA + 2 hB] is a nowhere-zero 4-flow (Tutte), hence a circular [r]-flow for every [r > 4].

The implication is the edge e096 of relations.json in graph-conjectures.  It was formalized in
graph-theory-rocq (cycle-theory/theories/conjectures/implications_D1.v). *)

From GraphTheory Require Import mgraph.
From GraphTheory Require Import preliminaries digraph sgraph coloring dom.
From mathcomp Require Import boot order algebra.
From GC.GraphLib Require Import misc chromatic cycle even_subgraph flow.
From GC.cycle.OPG_odd_r_graph_circular_flow_bound Require Import
  main(OPG_odd_r_graph_circular_flow_bound).
From GC.cycle.OPG_circular_flow_number_regular_class_1 Require Import
  main(OPG_circular_flow_number_regular_class_1).

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Num.Theory Order.TTheory.

Section ColourClasses.
Variables (G : mgraph) (P : {set {set edge G}}).
Hypotheses (ll : mloopless G) (colP : @coloring (mline_graph G) P [set: edge G])
  (reg : mregular G #|P|).

Let covP : cover P = [set: edge G]. Proof. by case/andP: colP => /and3P[/eqP]. Qed.
Let trivP : trivIset P. Proof. by case/andP: colP => /and3P[]. Qed.

(** The colour classes are perfect matchings: the [#|P|] edges at a vertex have distinct colours,
    so each colour appears exactly once. *)
Lemma colour_class_perfect M v : M \in P -> mdeg_in M v = 1%N.
Proof.
move=> MP; rewrite mdeg_in_loopless //.
have inP e : pblock P e \in P by rewrite pblock_mem // covP.
have inB e : e \in pblock P e by rewrite mem_pblock covP.
have adj e f : e \in edges_at v -> f \in edges_at v -> e != f -> @edge_rel (mline_graph G) e f.
  move=> ev fv ef; rewrite /edge_rel /= /mline_rel ef; apply/existsP; exists v.
  by move: ev fv; rewrite !inE => -> ->.
have inj : {in edges_at v &, injective (pblock P)}.
  move=> e f ev fv ef; apply/eqP; apply: contraTT isT => nef.
  case/andP: colP => _ /forall_inP/(_ _ (inP e))/stableP st.
  by have := st e f (inB e) _; rewrite ef inB adj // => /(_ isT).
have onto : pblock P @: edges_at v = P.
  apply/eqP; rewrite eqEcard card_in_imset // reg leqnn andbT.
  by apply/subsetP => B /imsetP[e _ ->]; apply: inP.
move: MP; rewrite -onto => /imsetP[e ev ->]; apply/eqP/cards1P; exists e; apply/setP => f.
rewrite !inE; apply/andP/eqP => [[fB fv]|->]; last by rewrite inB; move: ev; rewrite inE.
apply: inj; rewrite ?inE //; first by move: ev; rewrite inE.
by apply: def_pblock => //; apply: inP.
Qed.

(** A perfect matching meets every odd cut. *)
Lemma colour_class_cut M (X : {set G}) : M \in P -> odd #|X| -> (0 < #|M :&: mcut X|)%N.
Proof.
move=> MP oddX; rewrite lt0n; apply: contraTneq oddX => cX.
rewrite -[#|X|]sum1_card -(eq_bigr _ (fun v _ => colour_class_perfect v MP)).
by rewrite odd_mdeg_sum cX.
Qed.

(** The graph is a [#|P|]-graph. *)
Lemma colour_r_graph : r_graph G #|P|.
Proof.
split=> // X oddX; rewrite -sum1_card -[#|mcut X|]sum1_card.
rewrite (partition_big (pblock P) (mem P)) => [e _|].
  by apply: pblock_mem; rewrite covP inE.
apply: leq_sum => M MP; have /card_gt0P[e /setIP[eM eX]] := colour_class_cut MP oddX.
by rewrite (bigD1 e) //= eX (def_pblock trivP MP eM) eqxx.
Qed.

End ColourClasses.

(** [a + 2 b] is a nowhere-zero 4-flow value when [a] and [b] are in [{-1, 0, 1}], not both 0. *)
Lemma four_flow_value (a b : int) :
  (`|a| <= 1 -> `|b| <= 1 -> (a != 0) || (b != 0) -> 1 <= `|a + 2 * b| <= 3)%R.
Proof. by case: a => [[|[|]]|[|]]; case: b => [[|[|]]|[|]]. Qed.

Theorem OPG_odd_r_graph_circular_flow_bound_implies_OPG_circular_flow_number_regular_class_1 :
  OPG_odd_r_graph_circular_flow_bound -> OPG_circular_flow_number_regular_class_1.
Proof.
move=> HA t G t1 G0 ll reg c1.
have D : mDelta G = (2 * t + 1)%N.
  apply/eqP; rewrite eqn_leq; apply/andP; split; first by apply/bigmax_leqP => v _; rewrite reg.
  by case/card_gt0P: G0 => v _; rewrite -(reg v) (leq_bigmax v).
have : mchromatic_index G = mDelta G := c1.
rewrite /mchromatic_index D; case: chiP => P colP _ cardP.
have regP : mregular G #|P| by rewrite cardP.
case: (ltnP 1 t) => [t1'|t1']; first by apply: HA => //; rewrite -cardP; apply: colour_r_graph.
(* t = 1: a nowhere-zero 4-flow from two colour classes. *)
have /eqP t_1 : t == 1 by rewrite eqn_leq t1 t1'.
subst t.
case/andP: (colP) => /and3P[_ trivP _] _.
have /card_gt1P[Ma [Mb [MaP MbP ab]]] : 1 < #|P| by rewrite cardP.
have ev M : M \in P -> even_subgraph (~: M).
  move=> MP v; rewrite mdeg_in_loopless // setIC -setDE.
  have := cardsID M (edges_at v); rewrite setIC -mdeg_in_loopless //.
  by rewrite (colour_class_perfect ll colP regP _ MP) regP cardP add1n => -[->].
have [oA bA] := even_balanced_orientation (ev _ MaP).
have [oB bB] := even_balanced_orientation (ev _ MbP).
pose g e := (osgn (~: Ma) oA e + 2 * osgn (~: Mb) oB e)%R.
have cg : conservative g.
  apply/conservativeE => v; rewrite mnetD mnetZ.
  move/conservativeE: (osgn_conservative bA) => ->.
  by move/conservativeE: (osgn_conservative bB) => ->; rewrite mulr0 addr0.
have bg e : (1 <= `|g e| <= 3)%R.
  apply: four_flow_value; rewrite ?normr_osgn ?inE ?lern1 ?leq_b1 //.
  rewrite -!normr_gt0 !normr_osgn !inE !ltr0n !lt0b -negb_and; apply/negP => /andP[ea eb].
  by have := trivIsetP trivP Ma Mb MaP MbP ab; move/disjointFr/(_ ea); rewrite eb.
move=> r hr; exists (fun e => (g e)%:~R)%R; split; first by move=> v; rewrite -!rmorph_sum (cg v).
move=> e; rewrite -intr_norm ler1z; have /andP[-> g3] := bg e; split=> //.
apply: (@le_trans _ _ (3%:R : rat)).
  by change (`|g e|%:~R <= (3 : int)%:~R :> rat)%R; rewrite ler_int.
by rewrite lerBrDr natr1 (le_trans _ (ltW hr)) // divr1 -natrD.
Qed.

Check (OPG_odd_r_graph_circular_flow_bound_implies_OPG_circular_flow_number_regular_class_1 :
  GC.cycle.OPG_odd_r_graph_circular_flow_bound.main.OPG_odd_r_graph_circular_flow_bound ->
  GC.cycle.OPG_circular_flow_number_regular_class_1.main.OPG_circular_flow_number_regular_class_1).
Print Assumptions OPG_odd_r_graph_circular_flow_bound_implies_OPG_circular_flow_number_regular_class_1.
