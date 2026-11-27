(** * Inflating the vertices into cycles: reduction of bridgeless multigraphs to cubic ones

Every vertex [v] of a multigraph [G] is replaced by a cycle through the ends of the edges at [v]
([inflate]): the vertices of the inflated graph are the ends of the edges of [G], each edge of [G]
joins its two ends, and the ends at [v] are joined by a cycle, in an arbitrary order.  If [G] is
bridgeless, the inflated graph is loopless, cubic and bridgeless, and connected if [G] is
connected, hence 2-connected ([cubic_2connected] of [misc]).  Contracting the cycles maps the even
subgraphs of the inflated graph to even subgraphs of [G] ([contract_even]).

This is the classical reduction of cycle covers of bridgeless graphs to cubic graphs (Jaeger, "A
survey of the cycle double cover conjecture", 1985). *)

From GraphTheory Require Import mgraph.
From mathcomp Require Import boot.
From GC.GraphLib Require Import misc cycle even_subgraph.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Inflate.
Variable G : mgraph.
Implicit Types (a b : edge G * bool) (v x y : G).

(** The end [a] of the edge [a.1] is at its target if [a.2], at its source otherwise. *)
Definition aend a : G := endpoint a.2 a.1.

(** The ends at [v], in the order of the cycle that replaces [v]. *)
Definition ends v : seq (edge G * bool) := enum [pred a | aend a == v].

(** The next and previous ends on the cycle. *)
Definition nxt a := next (ends (aend a)) a.
Definition prv a := prev (ends (aend a)) a.

(** The inflated graph: the copy [inl e] of an edge [e] joins its two ends, the edge [inr a] of a
    cycle joins [a] to [nxt a]. *)
Definition inflate : mgraph :=
  @Graph unit unit (edge G * bool)%type (edge G + (edge G * bool))%type
    (fun (d : bool) f => match f with inl e => (e, d) | inr a => if d then nxt a else a end)
    (fun=> tt) (fun=> tt).

Lemma mem_ends v a : (a \in ends v) = (aend a == v).
Proof. by rewrite mem_enum. Qed.

Lemma aend_nxt a : aend (nxt a) = aend a.
Proof. by apply/eqP; rewrite -mem_ends mem_next mem_ends. Qed.

Lemma nxtK : cancel nxt prv.
Proof. by move=> a; rewrite /prv aend_nxt prev_next // enum_uniq. Qed.

Lemma prvK : cancel prv nxt.
Proof.
by move=> a; rewrite /nxt (_ : aend (prv a) = aend a) ?next_prev ?enum_uniq //; apply/eqP;
  rewrite -mem_ends mem_prev mem_ends.
Qed.

(** The cycle of the ends at [aend a], from [a]. *)
Lemma nxt_cycle a : exists q : seq (edge G * bool),
  [/\ traject nxt a (size q).+1 = a :: q, iter (size q).+1 nxt a = a, uniq (a :: q)
    & a :: q =i ends (aend a)].
Proof.
set s := ends (aend a); have /rot_to[i q rq] : a \in s by rewrite mem_ends.
have tr n c : c \in s -> traject nxt c n = traject (next s) c n.
  elim: n c => //= n IH c cs; congr (_ :: _).
  have -> : nxt c = next s c by rewrite /nxt (eqP (_ : aend c == aend a)) // -mem_ends.
  by rewrite IH // mem_next.
have fc : fcycle (next s) (a :: q) by rewrite -rq rot_cycle cycle_next // enum_uniq.
exists q; split.
- by rewrite tr ?mem_ends // -fcycle_consE.
- have := fcycle_rconsE fc; rewrite -tr ?mem_ends // trajectSr tr ?mem_ends // -fcycle_consE //.
  by move/rcons_inj => [].
- by rewrite -rq rot_uniq enum_uniq.
- by move=> c; rewrite -rq mem_rot.
Qed.

(** Walks around the cycles. *)
Lemma walk_around a n : @uwalk inflate a (iter n nxt a) (map inr (traject nxt a n)).
Proof.
elim: n a => [a|n IH a]; first by rewrite /= eqxx.
by rewrite iterSr /= eqxx IH.
Qed.

Lemma reach a b : aend b = aend a -> exists n, iter n nxt a = b.
Proof.
move=> ba; have [q [tq _ _ mq]] := nxt_cycle a.
have : b \in traject nxt a (size q).+1 by rewrite tq mq mem_ends ba.
by case/trajectP => n _ ->; exists n.
Qed.

Lemma around a b : aend b = aend a -> exists cs, @uwalk inflate a b (map inr cs).
Proof.
by case/reach => n <-; exists (traject nxt a n); apply: walk_around.
Qed.

(** An edge of a cycle is not a bridge. *)
Lemma cycle_edge_not_bridge a : ~ mbridge (inr a : edge inflate).
Proof.
have [q [tq iq uq _]] := nxt_cycle a; move/(_ (rev (map inr q))).
rewrite mem_rev => /(_ _)/mapP[]; last by move=> c cq [ac]; move: uq; rewrite /= ac cq.
apply: uwalk_rev; have := walk_around (nxt a) (size q); rewrite -iterSr iq.
by move: tq => /= [->].
Qed.

(** A walk of [G] lifts to a walk of the inflated graph, between any ends of its extremities,
    through copies of its own edges. *)
Lemma lift x y (w : seq (edge G)) a b : uwalk x y w -> aend a = x -> aend b = y ->
  exists W, @uwalk inflate a b W /\ forall e, inl e \in W -> e \in w.
Proof.
elim: w x a => [|e w IH] x a /=.
  move=> /eqP <- ax bx; have [cs h] := around (etrans bx (esym ax)).
  by exists (map inr cs); split => // e /mapP[].
have step d : endpoint d e = x -> uwalk (endpoint (~~ d) e) y w -> aend a = x -> aend b = y ->
    exists W, @uwalk inflate a b W /\ forall g, inl g \in W -> g \in e :: w.
  move=> ex hw ax bx; have [cs h1] := around (etrans ex (esym ax) : aend (e, d) = aend a).
  have [W [h2 hW]] := IH _ (e, ~~ d) hw erefl bx.
  exists (map inr cs ++ inl e :: W); split.
    by apply: uwalk_cat h1 _; apply: (@uwalk_cat inflate _ _ _ [:: inl e] W _ h2);
      apply: (uwalk_edge (inl e : edge inflate) d).
  move=> g; rewrite mem_cat in_cons => /or3P[/mapP[]//|/eqP[->]|/hW gw];
    by rewrite in_cons ?eqxx ?gw ?orbT.
by case/orP => /andP[/eqP ex hw]; [apply: (step false) | apply: (step true)].
Qed.

Lemma inflate_bridgeless : bridgeless G -> bridgeless inflate.
Proof.
move=> bl [e|a]; last exact: cycle_edge_not_bridge.
move=> br; apply: (bl e) => w hw; apply/negPn/negP => ew.
have [W [hW hWw]] := lift (a := (e, false)) (b := (e, true)) hw erefl erefl.
by move: (hWw e (br W hW)); rewrite (negbTE ew).
Qed.

(** A vertex of a bridgeless graph is not of degree one: it has at least two ends. *)
Lemma nxt_neq : bridgeless G -> forall a, nxt a != a.
Proof.
move=> bl [e d]; apply/eqP => h.
have one f c : endpoint c f = aend (e, d) -> (f, c) = (e, d).
  by move=> fv; have [n <-] := reach (a := (e, d)) (b := (f, c)) fv; rewrite iter_fix.
have ov : endpoint (~~ d) e != endpoint d e by apply/eqP => /one[]; case: (d).
apply: (bl e) => w hw.
have [w' [hw' ->]] :
    exists w', uwalk (endpoint d e) (endpoint (~~ d) e) w' /\ (e \in w) = (e \in w').
  by case: (d) hw; [exists (rev w); rewrite mem_rev uwalk_rev | exists w].
case: w' hw' => [/eqP ex|f w' /orP[] /andP[/eqP /one[-> _] _]]; rewrite ?mem_head //.
by rewrite ex eqxx in ov.
Qed.

Lemma inflate_loopless : bridgeless G -> mloopless inflate.
Proof. by move=> bl [e|a] /=; [rewrite xpair_eqE andbF | rewrite eq_sym nxt_neq]. Qed.

Lemma inflate_cubic : bridgeless G -> mcubic inflate.
Proof.
move=> bl a; have -> : edges_at a = inl a.1 |: [set inr a; inr (prv a)].
  apply/setP => -[e|c]; rewrite !inE incidentE /=.
    by case: a => e' []; rewrite !xpair_eqE ?andbF ?andbT ?orbF.
  by rewrite (can2_eq nxtK prvK).
rewrite cardsU1 cards2 !inE /=.
suff -> : inr a != inr (prv a) :> edge inflate by [].
by apply: contraNneq (nxt_neq bl a) => -[{1}->]; rewrite prvK.
Qed.

(** The contraction of the cycles: the edges of [G] whose copy is in [C]. *)
Definition contract (C : {set edge inflate}) : {set edge G} := [set e | inl e \in C].

Lemma contract_even C : even_subgraph C -> even_subgraph (contract C).
Proof.
move=> Ce v; set S := [set a : inflate | aend a == v].
have := sum_mdeg_in C S; rewrite big_sumType /=.
have -> : \sum_(e | inl e \in C) (((e, false) \in S) + ((e, true) \in S)) = mdeg_in (contract C) v.
  by rewrite mdeg_inE; apply: eq_big => [e|e _]; rewrite !inE.
have -> : \sum_(c | inr c \in C) ((c \in S) + (nxt c \in S)) = 2 * \sum_(c | inr c \in C) (c \in S).
  by rewrite big_distrr; apply: eq_bigr => c _; rewrite !inE aend_nxt addnn -mul2n.
move=> /(congr1 odd); rewrite oddD oddM /= addbF => <-.
apply: (big_ind (fun n => ~~ odd n)) => [//|m n|a _]; last exact: Ce.
by rewrite oddD => /negbTE -> /negbTE ->.
Qed.

(** If [G] is connected, so is its inflation. *)
Lemma inflate_uwalk : (forall x y : G, exists w, uwalk x y w) ->
  forall a b : inflate, exists W, uwalk a b W.
Proof.
move=> con a b; have [w h] := con (aend a) (aend b).
by have [W [hW _]] := lift h erefl erefl; exists W.
Qed.

End Inflate.
