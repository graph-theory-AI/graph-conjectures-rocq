(** * Inflating the vertices of a multigraph into cycles of multiple edges

As in [GraphLib/cubic_inflation.v], every vertex [v] of [G] is replaced by a cycle through its
ends (the pairs [(e, b)] such that [endpoint b e = v], in the cyclic order [nxt]), and the edge
[e] of [G] joins the two ends of [e]; here the edges of the cycles have multiplicity [c].  When every
vertex with an edge has degree at least 2, the inflated graph is loopless and [(2c+1)]-regular.
A cut of the inflated graph either splits the cycle of a vertex, and has at least [2c] edges, or
is the cut of a set of vertices of [G], with the same number of edges.  Contracting the cycles
maps flows to flows.  Used with [c = 2] for 5-graphs and [c = 1] for cubic graphs. *)

From GraphTheory Require Import mgraph.
From GraphTheory Require Import preliminaries digraph sgraph.
From mathcomp Require Import boot order algebra.
From GC.GraphLib Require Import misc cycle cubic_inflation flow.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Num.Theory Order.TTheory.

Section Inflation.
Variables (G : mgraph) (c : nat).
Implicit Types (a : edge G * bool).

(** The inflated graph: [inl e] joins the two ends of [e], and [inr (a, i)], for [i < c], joins
    [a] to the next end around the same vertex. *)
Definition infl : mgraph :=
  @Graph unit unit (edge G * bool)%type (edge G + (edge G * bool) * 'I_c)%type
    (fun (t : bool) f =>
       match f with inl e => (e, t) | inr ai => if t then nxt ai.1 else ai.1 end)
    (fun _ => tt) (fun _ => tt).

Lemma infl_card : #|infl| = (2 * #|edge G|)%N.
Proof. by rewrite card_prod card_bool mulnC. Qed.

(** Along an orbit of [f], a predicate that holds at the start and fails later is left at some
    step. *)
Lemma iter_cross (T : Type) (f : T -> T) (P : pred T) (z : T) (n : nat) :
  P z -> ~~ P (iter n f z) -> exists i, P (iter i f z) && ~~ P (iter i.+1 f z).
Proof.
move=> hz; elim: n => [|n IH] /=; first by rewrite hz.
case hn: (P (iter n f z)); first by move=> hn1; exists n; rewrite hn hn1.
by move=> _; apply: IH; rewrite hn.
Qed.

(** A set that splits the ends of a vertex cuts its cycle at least twice, each time in [c]
    parallel edges. *)
Lemma infl_mcut_split (X : {set infl}) a (b : edge G * bool) :
  a \in X -> b \notin X -> aend b = aend a -> (2 * c <= #|mcut X|)%N.
Proof.
move=> aX bX ba.
have [n hn] := reach ba; have [n' hn'] := reach (esym ba).
have an : ~~ (iter n (@nxt G) a \in X) by rewrite hn.
have bn : ~~ ~~ (iter n' (@nxt G) b \in X) by rewrite hn' aX.
have [i /andP[hi hi1]] := @iter_cross _ (@nxt G) (fun x => x \in X) a n aX an.
have [j /andP[hj hj1]] := @iter_cross _ (@nxt G) (fun x => x \notin X) b n' bX bn.
move: hi hi1 hj hj1 => /= hi hi1 hj; rewrite negbK => hj1.
set x1 := iter i (@nxt G) a in hi hi1; set x2 := iter j (@nxt G) b in hj hj1.
have cut x k : (x \in X) != (nxt x \in X) -> (inr (x, k) : edge infl) \in mcut X.
  by rewrite inE /=; case: (x \in X); case: (nxt x \in X).
have x12 : x1 != x2 by apply: contraNneq hj => <-.
pose E := [set (inr (x1, k) : edge infl) | k in 'I_c]
          :|: [set (inr (x2, k) : edge infl) | k in 'I_c].
have inj x : injective (fun k : 'I_c => (inr (x, k) : edge infl)) by move=> k k' [].
apply: leq_trans (_ : #|E| <= _)%N; last first.
  by apply/subset_leq_card/subsetP => f; rewrite inE => /orP[]/imsetP[k _ ->]; apply: cut;
    rewrite ?hi ?hi1 ?(negbTE hj) ?hj1.
rewrite cardsU (_ : _ :&: _ = set0) ?cards0 ?subn0 ?card_imset // ?card_ord ?mul2n ?addnn //.
apply/setP => f; rewrite !inE; apply/negP => /andP[/imsetP[k _ ->] /imsetP[k' _ [e12 _]]].
by rewrite e12 eqxx in x12.
Qed.

(** A union of whole cycles cuts the copies of the edges of the corresponding cut of [G]. *)
Lemma infl_mcut_union (S : {set G}) : #|@mcut infl [set a | aend a \in S]| = #|mcut S|.
Proof.
rewrite -[RHS](card_imset _ (@inl_inj (edge G) ((edge G * bool) * 'I_c)%type)).
apply: eq_card => -[e|[a k]].
  by rewrite (mem_imset _ _ (@inl_inj _ _)) !inE.
rewrite !inE /= aend_nxt addbb; apply/esym/negbTE/imsetP => -[e _] //.
Qed.

(** A cut of the inflated graph splits a cycle or is the cut of a union of cycles. *)
Lemma infl_mcut (X : {set infl}) :
  (2 * c <= #|mcut X|)%N \/ exists S : {set G}, X = [set a | aend a \in S].
Proof.
have [/existsP[a /existsP[b /and3P[aX bX /eqP ba]]]|nosplit] :=
  boolP [exists a : infl, exists b : infl, [&& a \in X, b \notin X & aend b == aend a]].
  by left; apply: infl_mcut_split aX bX ba.
right; exists [set v | [exists a : infl, (a \in X) && (aend a == v)]].
apply/setP => a; rewrite !inE; apply/idP/existsP => [aX|[b /andP[bX /eqP ba]]].
  by exists a; rewrite aX eqxx.
apply: contraNT nosplit => aX; apply/existsP; exists b; apply/existsP; exists a.
by rewrite bX aX ba eqxx.
Qed.

(** A union of whole cycles with an odd number of ends comes from a set of vertices of [G] that is
    neither empty nor full. *)
Lemma infl_union_odd (S : {set G}) :
  odd #|[set a : infl | aend a \in S]| -> exists x y, x \in S /\ y \notin S.
Proof.
move=> oddS; have [S0|[x xS]] := set_0Vmem S.
  move: oddS; rewrite (_ : [set a : infl | _] = set0) ?cards0 //.
  by apply/setP => a; rewrite S0 !inE.
have [ST|[y yS]] := set_0Vmem (~: S); last by exists x, y; rewrite inE in yS.
move: oddS; rewrite (_ : [set a : infl | _] = setT) ?cardsT ?infl_card ?mul2n ?odd_double //.
by apply/setP => a; rewrite -(setCK S) ST setC0 !inE.
Qed.

(** Contracting the cycles: the values on the copies of the edges of [G] form a flow of [G], since
    the cycle edges of [v] count for 0 in the net outflow of the ends of [v]. *)
Lemma infl_contract (psi : edge infl -> int) :
  conservative psi -> conservative (fun e => psi (inl e)).
Proof.
move/conservativeE => hc; apply/conservativeE => v.
have := sum_mnet_sign psi [set a : infl | aend a == v]; rewrite big1 => [a _|]; first exact: hc.
rewrite big_sumType /= [X in (_ + X)%R]big1 ?addr0 => [[a k] _|].
  by rewrite !inE aend_nxt subrr mulr0.
by move=> ->; rewrite mnetE; apply: eq_bigr => e _; rewrite !inE.
Qed.

(** If no cut of [G] has exactly one edge, every vertex with an end has at least two of them. *)
Lemma infl_nxt_neq : (forall S : {set G}, #|mcut S| != 1%N) -> forall a, nxt a != a.
Proof.
move=> no1 [e0 t0]; apply/negP => /eqP na; have /eqP[] := no1 [set aend (e0, t0)].
have only b : aend b = aend (e0, t0) -> b = (e0, t0).
  by case/reach => n <-; elim: n => //= n ->.
apply/eqP/cards1P; exists e0; apply/setP => e; rewrite !inE.
have endv t : (endpoint t e == aend (e0, t0)) = (e == e0) && (t == t0).
  apply/eqP/andP => [/(only (e, t))[-> ->]|[/eqP-> /eqP->]] //.
by rewrite !endv; case: (e == e0) => //; case: (t0).
Qed.

Hypothesis nn : forall a, nxt a != a.

Lemma infl_loopless : mloopless infl.
Proof. by case=> [e|[a i]] /=; [rewrite xpair_eqE eqxx | rewrite eq_sym nn]. Qed.

Lemma infl_regular : mregular infl (2 * c).+1.
Proof.
move=> a; rewrite mloopless_edges_at /mdeg /mdeg_in; first exact: infl_loopless.
have cyc (P : pred (edge G * bool)) : #|[set y : (edge G * bool) * 'I_c | P y.1]| = (#|P| * c)%N.
  transitivity #|setX [set x | P x] [set: 'I_c]|.
    by apply: eq_card => -[x i]; rewrite !inE andbT.
  by rewrite cardsX cardsT card_ord cardsE.
have ends t : #|[set f in [set: edge infl] | endpoint t f == a]| =
    ((a.2 == t) + #|[set y : (edge G * bool) * 'I_c | endpoint t (inr y : edge infl) == a]|)%N.
  rewrite -!sum1_card big_sumType /=; congr (_ + _)%N; last by apply: eq_bigl => y; rewrite !inE.
  case: a => e t'; rewrite (eq_bigl (fun x => (x == e) && (t == t'))) => [x|].
    by rewrite !inE xpair_eqE.
  rewrite /= eq_sym; case: (t' == t); last by rewrite big_pred0 // => x; rewrite andbF.
  by rewrite (eq_bigl (pred1 e)) ?big_pred1_eq // => x; rewrite andbT.
rewrite !ends /= (cyc (pred1 a)) (cyc [pred x | nxt x == a]) card1.
rewrite (_ : #|[pred x | nxt x == a]| = 1%N).
  by rewrite -(card1 (prv a)); apply: eq_card => x; rewrite !inE (can2_eq (@nxtK G) (@prvK G)).
by rewrite !mul1n mul2n -addnn; case: (a.2); rewrite /= add0n add1n ?addnS.
Qed.

End Inflation.
