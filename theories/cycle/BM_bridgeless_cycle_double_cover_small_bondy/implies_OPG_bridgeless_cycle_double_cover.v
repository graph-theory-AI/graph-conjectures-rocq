(** * Bondy's small cycle double cover conjecture implies the cycle double cover conjecture

Bondy's conjecture is stated for simple graphs; forgetting the bound on the number of cycles, it is
the cycle double cover conjecture for simple graphs.  The general case reduces to it by subdividing
every edge twice: the edge [e] becomes a path of three edges [(e, Some false)], [(e, None)],
[(e, Some true)] through two new vertices.  The subdivided graph is simple (a loop becomes a
triangle, parallel edges become internally disjoint paths) and bridgeless (a walk of the graph lifts
to the subdivided graph).  A cycle of the subdivided graph contains the three edges of [e] or none
of them, and its middle edges form a cycle of the graph, so that a cycle double cover of the
subdivided graph gives one of the graph.

This classical reduction is the relation e209 of graph-conjectures.  It was formalized in
graph-theory-rocq (cycle-theory/theories/conjectures/implications_U6.v). *)

From GraphTheory Require Import mgraph.
From mathcomp Require Import boot.
From GC.GraphLib Require Import misc chromatic(msimple).
From GC.cycle.BM_bridgeless_cycle_double_cover_small_bondy Require Import
  main(BM_bridgeless_cycle_double_cover_small_bondy).
From GC.cycle.OPG_bridgeless_cycle_double_cover Require Import
  main(OPG_bridgeless_cycle_double_cover).

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** A walk along [w1 ++ w2] passes at the end of [w1]. *)
Lemma uwalk_split (G : mgraph) (x z : G) w1 w2 :
  uwalk x z (w1 ++ w2) -> exists y, uwalk x y w1 /\ uwalk y z w2.
Proof.
elim: w1 x => [x h|e w1 IH x /= /orP[]/andP[ex /IH[y [h1 h2]]]]; first by exists x; rewrite /=.
  by exists y; rewrite ex h1.
by exists y; rewrite ex h1 orbT.
Qed.

(** If [P] holds exactly at [a], the number of elements of [C] satisfying [P] is [a \in C]. *)
Lemma card_eq1 (T : finType) (C : {set T}) (P : pred T) (a : T) :
  (forall x, P x = (x == a)) -> #|[set x in C | P x]| = (a \in C).
Proof.
move=> Pa; rewrite (cardsD1 a) !inE Pa eqxx andbT -[RHS]addn0; congr (_ + _).
by apply: eq_card0 => x; rewrite !inE Pa; case: (x == a); rewrite ?andbF.
Qed.

Section Subdivision.
Variable G : mgraph.

(** The ends of the edges of the subdivision: [(e, None)] joins the new vertices [inr (e, false)]
    and [inr (e, true)], and [(e, Some c)] joins [inr (e, c)] to the end [endpoint c e] of [e]. *)
Definition sd_end (b : bool) (f : edge G * option bool) : G + (edge G * bool) :=
  match f.2 with
  | None => inr (f.1, b)
  | Some c => if b == c then inl (endpoint c f.1) else inr (f.1, c)
  end.

Definition sdG : mgraph :=
  @Graph unit unit (G + (edge G * bool))%type (edge G * option bool)%type sd_end
    (fun _ => tt) (fun _ => tt).

(** The vertex of [G] below a vertex of [sdG]. *)
Definition sd_pi (x : sdG) : G := match x with inl v => v | inr (e, c) => endpoint c e end.

(** The middle edges of a set of edges of [sdG]. *)
Definition sd_back (C : {set edge sdG}) : {set edge G} := [set e | ((e, None) : edge sdG) \in C].

(** The three edges of [e], from [source e] to [target e]. *)
Definition sd_path (e : edge G) : seq (edge sdG) := [:: (e, Some false); (e, None); (e, Some true)].
Arguments sd_path : simpl never.

Fixpoint sd_lift (x : G) (w : seq (edge G)) : seq (edge sdG) :=
  if w is e :: w' then
    if source e == x then sd_path e ++ sd_lift (target e) w'
    else rev (sd_path e) ++ sd_lift (source e) w'
  else [::].

(** [sdG] is simple: an edge is determined by its two ends. *)
Lemma sd_simple : msimple sdG.
Proof.
split=> [[e [[]|]] //|[e1 k1] [e2 k2] h]; first by apply/eqP => -[].
pose s := sd_end false (e1, k1); pose t := sd_end true (e1, k1).
move: (set21 s t) (set22 s t); rewrite [in X in X -> _]h [in X in _ -> X]h.
move=> /set2P + /set2P; rewrite {}/s {}/t; clear h.
by case: k1 k2 => [[]|] [[]|]; rewrite /= /sd_end /= => -[] h1 [] h2; congruence.
Qed.

Lemma sd_path_uwalk e : uwalk (inl (source e) : sdG) (inl (target e)) (sd_path e).
Proof. by rewrite /sd_path /= /sd_end /= !eqxx. Qed.

Lemma sd_lift_cons x e w : sd_lift x (e :: w) =
  if source e == x then sd_path e ++ sd_lift (target e) w
  else rev (sd_path e) ++ sd_lift (source e) w.
Proof. by []. Qed.

Lemma sd_lift_uwalk x y w : uwalk x y w -> uwalk (inl x : sdG) (inl y) (sd_lift x w).
Proof.
elim: w x => [x /eqP -> /=|e w IH x /orP[]/andP[/eqP <- h]]; first exact: eqxx.
  by rewrite sd_lift_cons eqxx; apply: uwalk_cat (sd_path_uwalk e) (IH _ h).
rewrite sd_lift_cons; case: ifP => [/eqP st|_].
  by rewrite -{1}st; apply: (uwalk_cat (sd_path_uwalk e)); apply: IH; rewrite -st.
exact: uwalk_cat (uwalk_rev (sd_path_uwalk e)) (IH _ h).
Qed.

Lemma sd_lift_mem x w (f : edge sdG) : f \in sd_lift x w -> f.1 \in w.
Proof.
elim: w x => [//|e w IH x]; rewrite sd_lift_cons.
have pe : f \in sd_path e -> f.1 = e by rewrite /sd_path !inE => /or3P[]/eqP->.
by case: ifP => _; rewrite mem_cat ?mem_rev inE => /orP[/pe ->|/IH ->]; rewrite ?eqxx ?orbT.
Qed.

(** A bridge [(e, k)] of [sdG] would make [e] a bridge of [G]: a walk of [G] between the ends of
    [e] avoiding [e] lifts to a walk between the ends of [(e, k)] avoiding the three edges of [e],
    which can be completed by the two other edges of [e]. *)
Lemma sd_bridgeless : bridgeless G -> bridgeless sdG.
Proof.
move=> bl [e k] br; apply: (bl e) => w ew; apply/negPn/negP => ew'.
pose L := sd_lift (source e) w; have Lw : uwalk _ _ L := sd_lift_uwalk ew.
have uL : uniq (sd_path e) by rewrite /sd_path /= !inE !xpair_eqE /= eqxx.
have ek : ((e, k) : edge sdG) \in sd_path e by case: k {br} => [[]|]; rewrite !inE eqxx ?orbT.
move: (sd_path_uwalk e) uL; case/splitPr: ek => p1 p2 /uwalk_split[y [h1 h2]].
rewrite cat_uniq /= negb_or => /and4P[_ /andP[/negbTE f1 _] /negbTE f2 _].
have nW (z : sdG) : uwalk z (inl (target e)) p2 -> uwalk z y (p2 ++ rev L ++ p1) /\
    ((e, k) : edge sdG) \notin p2 ++ rev L ++ p1.
  move=> h; rewrite (uwalk_cat h (uwalk_cat (uwalk_rev Lw) h1)) !mem_cat mem_rev f1 f2 orbF.
  by split => //; apply/negP => /sd_lift_mem; apply/negP.
case/orP: h2 => /andP[/eqP fy /nW[W nf]]; rewrite -fy in W; move: nf.
  by rewrite -mem_rev (br _ _) //; exact: uwalk_rev W.
by rewrite (br _ _).
Qed.

Lemma sd_proj_uwalk (x y : sdG) (w : seq (edge sdG)) :
  uwalk x y w -> uwalk (sd_pi x) (sd_pi y) [seq f.1 | f <- w & f.2 == None].
Proof.
elim: w x => [x /eqP -> /=|[e [c|]] w IH x /= /orP[]/andP[/eqP <- /IH]]; first exact: eqxx.
- by case: c; rewrite /sd_end /=.
- by case: c; rewrite /sd_end /=.
- by rewrite /sd_end /= => ->; rewrite eqxx.
by rewrite /sd_end /= => ->; rewrite eqxx orbT.
Qed.

(** In a 2-regular set of edges of [sdG], the three edges of [e] are all in or all out: each new
    vertex [inr (e, c)] is the end of exactly two of them. *)
Lemma sd_reg (C : {set edge sdG}) e c :
  subgraph_kregular C 2 -> (((e, Some c) : edge sdG) \in C) = ((e, None) \in C).
Proof.
move=> reg; have := reg (inr (e, c)); rewrite /mdeg_in.
have hs (f : edge sdG) : (source f == inr (e, c)) = (f == (e, if c then Some true else None)).
  by case: f => g [[]|]; case: (c); rewrite /= /sd_end /=; apply/eqP/eqP => h; congruence.
have ht (f : edge sdG) : (target f == inr (e, c)) = (f == (e, if c then None else Some false)).
  by case: f => g [[]|]; case: (c); rewrite /= /sd_end /=; apply/eqP/eqP => h; congruence.
rewrite (card_eq1 _ hs) (card_eq1 _ ht); clear hs ht.
by case: c; case: (_ \in C); case: (_ \in C) => // -[].
Qed.

(** The degrees at the old vertices are the same in [C] and in its middle edges. *)
Lemma sd_mdeg (C : {set edge sdG}) v :
  subgraph_kregular C 2 -> mdeg_in (sd_back C) v = mdeg_in C (inl v).
Proof.
move=> reg; have inj b : injective (fun g => (g, Some b) : edge sdG) by move=> g1 g2 [].
suff hb b : #|[set f in C | endpoint b f == inl v]| = #|[set g in sd_back C | endpoint b g == v]|.
  by rewrite /mdeg_in !hb.
rewrite -(card_imset _ (inj b)); apply: eq_card => -[g k]; rewrite inE.
apply/andP/imsetP => [[gC]|[g' ]].
  case: k gC => [c|] gC; rewrite /= /sd_end /= => /eqP //; case: eqP => [bc [ev]|//]; subst c.
  by exists g; rewrite // !inE -(sd_reg g b reg) gC ev eqxx.
rewrite !inE => /andP[g'C /eqP ev] [-> ->].
by rewrite (sd_reg g' b reg) g'C /= /sd_end /= eqxx ev eqxx.
Qed.

(** The middle edges of a cycle of [sdG] form a cycle of [G]. *)
Lemma sd_circuit (C : {set edge sdG}) : is_circuit C -> is_circuit (sd_back C).
Proof.
case=> C0 reg con; split.
- case/set0Pn: C0 => -[g k] gC; apply/set0Pn; exists g; rewrite inE.
  by case: k gC => [c|] //; rewrite (sd_reg g c reg).
- by move=> v; rewrite sd_mdeg //; exact: reg.
move=> x y hx hy.
have lift z : subgraph_incident (sd_back C) z -> subgraph_incident C (inl z : sdG).
  case/existsP => g /andP[]; rewrite inE => gC /existsP[b /eqP gz].
  apply/existsP; exists (g, Some b); rewrite (sd_reg g b reg) gC /=.
  by apply/existsP; exists b; rewrite /= /sd_end /= eqxx gz.
have [w /andP[wu wC]] := con _ _ (lift _ hx) (lift _ hy).
exists [seq f.1 | f <- w & f.2 == None]; apply/andP; split; first exact: (sd_proj_uwalk wu).
apply/allP => g /mapP[[g' k]]; rewrite mem_filter /= => /andP[/eqP k0 gw ->].
by rewrite inE -k0 (allP wC _ gw).
Qed.

End Subdivision.

Theorem BM_bridgeless_cycle_double_cover_small_bondy_implies_OPG_bridgeless_cycle_double_cover :
  BM_bridgeless_cycle_double_cover_small_bondy -> OPG_bridgeless_cycle_double_cover.
Proof.
move=> BM G G0 _ bl.
have [|L [[Lc Ln] _]] := BM (sdG G) _ (sd_simple G) (sd_bridgeless bl).
  by case/card_gt0P: G0 => v _; apply/card_gt0P; exists (inl v).
exists (map (@sd_back G) L); split => [C /mapP[C' /Lc C'c ->]|e]; first exact: sd_circuit.
by rewrite count_map -(Ln (e, None)); apply: eq_count => C; rewrite /= inE.
Qed.

Check (BM_bridgeless_cycle_double_cover_small_bondy_implies_OPG_bridgeless_cycle_double_cover :
  GC.cycle.BM_bridgeless_cycle_double_cover_small_bondy.main.BM_bridgeless_cycle_double_cover_small_bondy ->
  GC.cycle.OPG_bridgeless_cycle_double_cover.main.OPG_bridgeless_cycle_double_cover).
Print Assumptions
  BM_bridgeless_cycle_double_cover_small_bondy_implies_OPG_bridgeless_cycle_double_cover.
