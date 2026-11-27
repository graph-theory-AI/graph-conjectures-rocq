(** * Reduction of the cycle double cover conjecture to graphs without small separating cuts

If every bridgeless graph with an edge whose cuts separating two vertices have at least three edges
has a cycle double cover, then so does every bridgeless graph with an edge
([cdc_small_cut_reduction]).

By strong induction on the number of vertices, every bridgeless graph [G] with an edge has a double
cover by even subgraphs.  If a cut separating two vertices has fewer than three edges, it has 0 or
2 edges, since [G] is bridgeless.  Identify two vertices on both sides of the cut (the ends of one
of its edges if it has 2 edges): the graph obtained is bridgeless, with fewer vertices and the same
edges.  An even double cover of it is one of [G], after toggling, for a cut [{e, f}], the edge [e]
in the subgraphs containing exactly one of [e] and [f]: the parity of the degree of the vertex on
the side [S] of the cut comes from the sum of the degrees on [S] ([odd_mdeg_sum]).  Finally,
the even subgraphs split into cycles with the same multiplicities (Veblen's theorem).

The reduction is classical.  This proof comes from graph-theory-rocq
(cycle-theory/theories/conjectures/implications_D1.v). *)

From GraphTheory Require Import mgraph.
From mathcomp Require Import boot.
From GC.GraphLib Require Import misc cycle even_subgraph.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** A double cover by even subgraphs. *)
Definition even_double_cover (G : mgraph) (L : seq {set edge G}) : Prop :=
  (forall C, C \in L -> even_subgraph C) /\
  forall e : edge G, count (fun C : {set edge G} => e \in C) L = 2.

(** ** Identifying two vertices *)

Section Identification.
Variables (G : mgraph) (u w : G).
Hypothesis uw : u != w.

(** The vertex [w] is identified with [u]. *)
Definition idpr (v : G) : {v : G | v != w} := insubd (exist _ u uw) v.

Definition identG : mgraph :=
  @Graph unit unit {v : G | v != w} (edge G) (fun b e => idpr (endpoint b e))
    (fun _ => tt) (fun _ => tt).

Lemma identG_card : #|identG| < #|G|.
Proof.
rewrite card_sig (eq_card (B := predC1 w)) // cardC1 ltn_predL.
by apply/card_gt0P; exists w.
Qed.

Lemma identG_uwalk x y p : uwalk x y p -> @uwalk identG (idpr x) (idpr y) p.
Proof.
by elim: p x => [x /eqP -> /=|e p IH x /= /orP[]/andP[/eqP <- /IH ->]]; rewrite ?eqxx ?orbT.
Qed.

Lemma identG_bridgeless : bridgeless G -> bridgeless identG.
Proof. by move=> bl e br; apply: (bl e) => p /identG_uwalk; exact: br. Qed.

Lemma identG_mdeg (C : {set edge G}) v : v != w ->
  @mdeg_in identG C (idpr v) = mdeg_in C v + (v == u) * mdeg_in C w.
Proof.
move=> vw; have h a : (idpr a == idpr v : nat) = (a == v) + (v == u) * (a == w).
  rewrite -val_eqE !val_insubd vw /=; case: (a =P w) => [->|/eqP aw].
    by rewrite /= eq_sym [w == v]eq_sym (negbTE vw) muln1.
  by rewrite muln0 addn0.
rewrite !mdeg_inE big_distrr -big_split; apply: eq_bigr => e _ /=.
by rewrite !h mulnDr addnACA.
Qed.

End Identification.

(** ** Lifting even subgraphs *)

Section Lifting.
Variable G : mgraph.
Implicit Types (C : {set edge G}) (S : {set G}).

(** Toggle [e] in [C] when [C] holds exactly one of [e] and [f]. *)
Definition tog (e f : edge G) C :=
  if (e \in C) == (f \in C) then C else if e \in C then C :\ e else e |: C.

Lemma tog_mem e f C g : g != e -> (g \in tog e f C) = (g \in C).
Proof. by move=> ge; rewrite /tog; do 2 case: ifP => //; rewrite !inE (negbTE ge). Qed.

Lemma tog_e e f C : e != f -> (e \in tog e f C) = (f \in C).
Proof.
by move=> ef; rewrite /tog; case: ifP => [/eqP //|]; case: (e \in C); case: (f \in C);
  rewrite //= !inE eqxx.
Qed.

(** The number of ends of [e] at [v]. *)
Definition nends (e : edge G) (v : G) : nat := (source e == v) + (target e == v).

Lemma mdeg_in_tog e f C v : e != f ->
  mdeg_in (tog e f C) v + (e \in C) * nends e v = mdeg_in C v + (f \in C) * nends e v.
Proof.
move=> ef; have split X :
    mdeg_in X v = (e \in X) * nends e v + \sum_(g | g != e) (g \in X) * nends g v.
  rewrite mdeg_inE big_mkcond (bigD1 e) //=; congr (_ + _).
    by rewrite /nends; case: (e \in X); rewrite ?mul1n.
  by apply: eq_bigr => g _; rewrite /nends; case: (g \in X); rewrite ?mul1n.
rewrite !split tog_e // addnAC [RHS]addnAC [X in X + _ = _]addnC; congr (_ + _).
by apply: eq_bigr => g ge; rewrite tog_mem.
Qed.

(** Let [C] be an even subgraph of the graph where [y] is identified with [x], and [C'] a set of
    edges with the same parities of degrees at the other vertices, and of the sum of the degrees at
    [x] and [y].  If [C'] meets the cut of [S] in an even number of edges, [C'] is even. *)
Lemma even_lift S x y (xy : x != y) C C' : x \in S -> y \notin S ->
  @even_subgraph (identG xy) C ->
  (forall v, v != x -> v != y -> odd (mdeg_in C' v) = odd (mdeg_in C v)) ->
  odd (mdeg_in C' x + mdeg_in C' y) = odd (mdeg_in C x + mdeg_in C y) ->
  ~~ odd #|C' :&: mcut S| -> even_subgraph C'.
Proof.
move=> xS yS ev oth sum cut.
have ev1 v : v != y -> ~~ odd (mdeg_in C v + (v == x) * mdeg_in C y).
  by move=> vy; rewrite -identG_mdeg //; exact: ev.
have evo v : v != x -> v != y -> ~~ odd (mdeg_in C' v).
  by move=> vx vy; rewrite oth //; have := ev1 v vy; rewrite (negbTE vx) addn0.
have evx : ~~ odd (mdeg_in C' x).
  move: cut; rewrite -odd_mdeg_sum (bigD1 x) //= oddD; apply: contra => ox.
  rewrite ox addTb; elim/big_ind: _ => // [a b|v /andP[vS vx]].
    by rewrite oddD => /negbTE -> /negbTE ->.
  by apply: evo => //; apply: contraNneq yS => <-.
move=> v; have [->|vx] := eqVneq v x => //; have [->|vy] := eqVneq v y; last exact: evo.
by have := ev1 x xy; rewrite eqxx mul1n -sum oddD (negbTE evx).
Qed.

End Lifting.

(** ** The reduction *)

(** If every bridgeless graph whose separating cuts have at least three edges has a cycle double
    cover, every bridgeless graph has a double cover by even subgraphs. *)
Lemma even_double_cover_reduction :
  (forall G : mgraph, 0 < #|edge G| -> bridgeless G ->
     (forall (S : {set G}) x y, x \in S -> y \notin S -> 2 < #|mcut S|) ->
   exists L : seq {set edge G}, cycle_double_cover L) ->
  forall G : mgraph, 0 < #|edge G| -> bridgeless G ->
  exists L : seq {set edge G}, even_double_cover L.
Proof.
move=> H3 G; move: {2}#|G| (leqnn #|G|) => n; elim: n G => [|n IH] G Gn E0 bl.
  by case/card_gt0P: E0 => e _; move: Gn; rewrite leqn0 => /eqP/card0_eq/(_ (source e)).
have [cut3|] := boolP [forall S : {set G}, [forall x, [forall y,
                         (x \in S) ==> (y \notin S) ==> (2 < #|mcut S|)]]].
  have [|L [Lc Ln]] := H3 G E0 bl.
    by move=> S x y xS yS; move/forallP/(_ S)/forallP/(_ x)/forallP/(_ y): cut3; rewrite xS yS.
  by exists L; split => // C /Lc [_ reg _] v; case: (reg v) => ->.
rewrite negb_forall => /existsP[S]; rewrite negb_forall => /existsP[x].
rewrite negb_forall => /existsP[y]; rewrite !negb_imply -leqNgt => /and3P[xS yS cut2].
have IH' (u w : G) (uw : u != w) : exists L, @even_double_cover (identG uw) L.
  apply: (IH (identG uw) _ E0 (@identG_bridgeless _ _ _ uw bl)).
  by rewrite -ltnS; apply: leq_trans Gn; exact: (@identG_card _ _ _ uw).
have [S0|[e eS]] := set_0Vmem (mcut S).
  (* an empty cut: identify [y] with [x] *)
  have xy : x != y by apply: contraNneq yS => <-.
  have [L [Lev Ln]] := IH' x y xy; exists L; split => // C CL.
  by apply: (even_lift xS yS (Lev C CL)) => //; rewrite S0 setI0 cards0.
(* a cut [{e, f}]: identify the ends of [e] *)
have [f fe Sef] : exists2 f, f != e & mcut S = [set e; f].
  have : #|mcut S| = 2 by apply/eqP; rewrite eqn_leq cut2 (bridgeless_mcut bl eS).
  rewrite (cardsD1 e) eS add1n => -[/eqP/cards1P[f Sf]].
  exists f; first by have := set11 f; rewrite -Sf !inE => /andP[].
  by rewrite -(setD1K eS) Sf.
have [x' [y' [x'S y'S ends]]] : exists x' y', [/\ x' \in S, y' \notin S &
    forall v, nends e v = (x' == v) + (y' == v)].
  move: eS; rewrite inE; case sS: (source e \in S) => /= tS.
    by exists (source e), (target e); split.
  by exists (target e), (source e); rewrite sS; split => // v; rewrite addnC.
have xy : x' != y' by apply: contraNneq y'S => <-.
have [L [Lev Ln]] := IH' x' y' xy; exists (map (tog e f) L); split => [C'|g]; last first.
  rewrite count_map; have [->|ge] := eqVneq g e; last first.
    by rewrite -(Ln g); apply: eq_count => C; rewrite /= tog_mem.
  by rewrite -(Ln f); apply: eq_count => C; rewrite /= tog_e // eq_sym.
case/mapP => C CL ->; have ef : e != f by rewrite eq_sym.
apply: (even_lift x'S y'S (Lev C CL)).
- move=> v vx vy; have := mdeg_in_tog C v ef.
  by rewrite ends ![_ == v]eq_sym (negbTE vx) (negbTE vy) !muln0 !addn0 => ->.
- have := congr2 addn (mdeg_in_tog C x' ef) (mdeg_in_tog C y' ef).
  rewrite !ends !eqxx (negbTE xy) [y' == x']eq_sym (negbTE xy) addnACA [RHS]addnACA -!mulnDr /=.
  by move/(congr1 odd); rewrite !oddD !oddM /= !andbF !addbF.
have -> : tog e f C :&: mcut S = if f \in C then [set e; f] else set0.
  apply/setP => g; rewrite Sef !inE; have [->|ge] := eqVneq g e.
    by rewrite tog_e // orTb andbT; case: (f \in C); rewrite !inE ?eqxx.
  rewrite tog_mem //=; have [->|gf] := eqVneq g f.
    by rewrite andbT; case: (f \in C); rewrite !inE ?eqxx ?orbT.
  by rewrite andbF; case: (f \in C); rewrite !inE ?(negbTE ge) ?(negbTE gf).
by case: (f \in C); rewrite ?cards2 ?ef ?cards0.
Qed.

Theorem cdc_small_cut_reduction :
  (forall G : mgraph, 0 < #|edge G| -> bridgeless G ->
     (forall (S : {set G}) x y, x \in S -> y \notin S -> 2 < #|mcut S|) ->
   exists L : seq {set edge G}, cycle_double_cover L) ->
  forall G : mgraph, 0 < #|edge G| -> bridgeless G ->
  exists L : seq {set edge G}, cycle_double_cover L.
Proof.
move=> H3 G E0 bl; have [L [Lev Ln]] := even_double_cover_reduction H3 E0 bl.
have [M [Mc Mn]] := even_subgraphs_cycles Lev; exists M; split => // e.
by rewrite Mn Ln.
Qed.
