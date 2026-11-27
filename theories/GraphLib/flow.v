(** * Existence of integer flows in multigraphs

The values of a flow are given in the reference direction of the edges (from [source] to
[target]); the net outflow ([mnet]) at a vertex is the sum of the values leaving it minus the sum
of those entering it.
- Hoffman's circulation theorem, 0/1 form ([demand_edge_set]): demands that sum to 0 are the net
  outflows of a set of edges of [A] if no set of vertices demands more than the number of edges
  of [A] leaving it.  The proof is by augmenting paths.
- Tutte's theorem ([mod_flow_lift]): a function whose net outflows are multiples of [k] is
  congruent modulo [k] to a flow with values of absolute value less than [k].  Hence a
  nowhere-zero Z_k-flow gives a nowhere-zero [k]-flow.
- Rounding ([rat_flow_round]): a rational flow within [eps] of the intervals [[l e, l e + 1]],
  with [m eps < 1] for [m] edges, gives an integer flow in these intervals (the argument of
  Goddyn, Tarsi and Zhang for circular flows).
- Flows of balanced orientations ([osgn_conservative]); parity of cuts in regular graphs; cuts
  of [k]-edge-connected graphs; multiplying the edges ([medge_mult]).
- Reduction: if every graph whose cuts separating two vertices have at least 3 edges has a
  nowhere-zero [k]-flow, then every bridgeless graph has one ([nowhere_zero_flow_reduction]). *)

From GraphTheory Require Import mgraph.
From GraphTheory Require Import preliminaries digraph sgraph.
From GraphTheory Require skeleton.
From mathcomp Require Import boot order algebra.
From GC.GraphLib Require Import misc cycle even_subgraph.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Num.Theory Order.TTheory.

Local Open Scope ring_scope.

(** ** Net outflows *)

Section Net.
Variables (G : mgraph) (V : zmodType).
Implicit Types (phi psi : edge G -> V) (S : {set G}).

(** The net outflow of [phi] at [v]. *)
Definition mnet phi (v : G) : V :=
  \sum_(e | source e == v) phi e - \sum_(e | target e == v) phi e.

Lemma conservativeE phi : conservative phi <-> forall v, mnet phi v = 0.
Proof.
by split=> h v; [rewrite /mnet h subrr | apply/eqP; rewrite -subr_eq0 -/(mnet phi v) h].
Qed.

Lemma eq_mnet phi psi : phi =1 psi -> mnet phi =1 mnet psi.
Proof. by move=> h v; rewrite /mnet !(eq_bigr _ (fun e _ => h e)). Qed.

Lemma mnetD phi psi v : mnet (fun e => phi e + psi e) v = mnet phi v + mnet psi v.
Proof. by rewrite /mnet !big_split /= opprD addrACA. Qed.

Lemma mnetN phi v : mnet (fun e => - phi e) v = - mnet phi v.
Proof. by rewrite /mnet !sumrN opprK opprB addrC. Qed.

Lemma mnet_sum (I : finType) (F : I -> edge G -> V) v :
  mnet (fun e => \sum_i F i e) v = \sum_i mnet (F i) v.
Proof.
by rewrite /mnet sumrB; congr (_ - _); rewrite (exchange_big_dep xpredT) //=;
  apply: eq_bigr => i _; apply: eq_bigl => e; rewrite andbT.
Qed.

(** The values at the [b]-ends in [S]. *)
Lemma sum_ends (b : bool) phi S :
  \sum_(v in S) \sum_(e | endpoint b e == v) phi e = \sum_(e | endpoint b e \in S) phi e.
Proof.
rewrite (exchange_big_dep (fun e => endpoint b e \in S)) /= => [v e vS /eqP -> //|].
apply: eq_bigr => e eS; rewrite (big_pred1 (endpoint b e)) // => v /=.
by rewrite eq_sym andbC; case: eqP => // ->.
Qed.

(** The net outflow of [S]: the values leaving [S] minus those entering it. *)
Lemma sum_mnet phi S :
  \sum_(v in S) mnet phi v =
  \sum_(e | (source e \in S) && (target e \notin S)) phi e
  - \sum_(e | (target e \in S) && (source e \notin S)) phi e.
Proof.
rewrite sumrB !sum_ends (bigID (fun e => target e \in S)) /=.
rewrite [X in _ - X](bigID (fun e => source e \in S)) /= opprD addrACA.
rewrite (eq_bigl (fun e => (target e \in S) && (source e \in S))) ?subrr ?add0r // => e.
exact: andbC.
Qed.

(** The net outflows sum to 0. *)
Lemma sum_mnetT phi : \sum_v mnet phi v = 0.
Proof.
transitivity (\sum_(v in [set: G]) mnet phi v); first by apply: eq_bigl => v; rewrite inE.
by rewrite sum_mnet !big_pred0 ?subrr // => e; rewrite !inE ?andbF.
Qed.

End Net.

Lemma mnetZ (G : mgraph) (R : pzRingType) (a : R) (phi : edge G -> R) v :
  mnet (fun e => a * phi e) v = a * mnet phi v.
Proof. by rewrite /mnet -!mulr_sumr mulrBr. Qed.

Section NetInt.
Variable G : mgraph.
Implicit Types (phi : edge G -> int).

(** The net outflow of a single edge. *)
Lemma mnet1 (e : edge G) v :
  mnet (fun f => (f == e)%:R) v = (source e == v)%:R - (target e == v)%:R :> int.
Proof.
suff h (P : pred (edge G)) : \sum_(f | P f) (f == e)%:R = (P e)%:R :> int by rewrite /mnet !h.
rewrite big_mkcond (bigD1 e) //= big1 => [f /negbTE-> |]; first by case: (P f).
by rewrite eqxx addr0; case: (P e).
Qed.

(** The net outflow of [S], edge by edge: [e] counts [+1] if it leaves [S] and [-1] if it enters
    it. *)
Lemma sum_mnet_sign phi (S : {set G}) :
  \sum_(v in S) mnet phi v = \sum_e phi e * ((source e \in S)%:R - (target e \in S)%:R).
Proof.
rewrite sumrB !sum_ends (big_mkcond (fun e => source e \in S)).
rewrite (big_mkcond (fun e => target e \in S)) -sumrB.
apply: eq_bigr => e _; rewrite mulrBr.
by case: (_ \in S); case: (_ \in S); rewrite ?mulr1 ?mulr0.
Qed.

(** The net outflow at [v], edge by edge. *)
Lemma mnetE phi v :
  mnet phi v = \sum_e phi e * ((source e == v)%:R - (target e == v)%:R).
Proof.
transitivity (\sum_(x in [set v]) mnet phi x); first by rewrite big_set1.
by rewrite sum_mnet_sign; apply: eq_bigr => e _; rewrite !inE.
Qed.

(** With the values [+1] along an orientation, the net outflow is minus the imbalance. *)
Lemma mnet_orient (o : edge G -> bool) v :
  mnet (fun e => if o e then 1 else -1) v = - orient_imbalance o v.
Proof.
rewrite mnetE /orient_imbalance opprB -!sum1_card !natr_sum.
rewrite [X in _ = X - _]big_mkcond [X in _ = _ - X]big_mkcond -sumrB; apply: eq_bigr => e _.
rewrite !inE /orient_head /orient_tail; case: (o e); rewrite ?mul1r ?mulN1r ?opprB.
  by case: (_ == v); case: (_ == v).
by case: (_ == v); case: (_ == v).
Qed.

(** The values ±1 along [o] on [C], and 0 elsewhere. *)
Definition osgn (C : {set edge G}) (o : edge G -> bool) (e : edge G) : int :=
  if e \in C then (if o e then 1 else -1) else 0.

Lemma normr_osgn (C : {set edge G}) (o : edge G -> bool) e : `|osgn C o e| = (e \in C)%:R.
Proof. by rewrite /osgn; case: (e \in C); case: (o e). Qed.

(** A balanced orientation of [C] gives a flow with values ±1 on [C]. *)
Lemma osgn_conservative (C : {set edge G}) (o : edge G -> bool) :
  balanced_orientation C o -> conservative (osgn C o).
Proof.
move=> bal; apply/conservativeE => v; rewrite mnetE.
have card (P : pred (edge G)) : \sum_(e in C) (P e)%:R = #|[set e in C | P e]|%:R :> int.
  rewrite -sum1_card natr_sum [RHS]big_mkcond [LHS]big_mkcond; apply: eq_bigr => e _.
  by rewrite inE; case: (e \in C); case: (P e).
transitivity (\sum_(e in C) ((orient_tail o e == v)%:R - (orient_head o e == v)%:R : int)).
  rewrite [RHS]big_mkcond; apply: eq_bigr => e _; rewrite /osgn /orient_tail /orient_head.
  by case: (e \in C); case: (o e); rewrite ?mul1r ?mulN1r ?opprB ?mul0r.
by rewrite sumrB !card bal subrr.
Qed.

End NetInt.

(** ** Hoffman's circulation theorem, 0/1 form *)

Section Hoffman.
Variables (G : mgraph) (A : {set edge G}).
Implicit Types (X : {set edge G}) (S : {set G}).

Local Abbreviation ind X := (fun e : edge G => (e \in X)%:R : int).

(** A residual step from [a] to [b]: an edge of [A] outside [X] from [a] to [b] (add it), or an
    edge of [X] from [b] to [a] (remove it).  Both increase the net outflow at [a] by one and
    decrease it at [b] by one. *)
Local Definition res_step X : rel G := fun a b =>
  [exists e, ((e \in A :\: X) && (source e == a) && (target e == b))
          || ((e \in X) && (target e == a) && (source e == b))].

Local Lemma res_step_toggle X a b : X \subset A -> res_step X a b ->
  exists (e : edge G), exists2 X' : {set edge G}, X' \subset A &
    [/\ forall f, (f \in X') = (f \in X) (+) (f == e),
        (source e == a) && (target e == b) || (target e == a) && (source e == b)
      & forall v, mnet (ind X') v = mnet (ind X) v + (v == a)%:R - (v == b)%:R].
Proof.
move=> XA /existsP[e /orP[]/andP[/andP[eX /eqP ea] /eqP eb]].
  case/setDP: eX => eA eX; exists e, (e |: X); first by rewrite subUset sub1set eA XA.
  split=> [f||v].
  - by rewrite !inE; case: eqP => [->|_]; rewrite ?(negbTE eX) ?orbF ?addbF.
  - by rewrite ea eb !eqxx.
  rewrite -addrA (eq_sym v a) (eq_sym v b) -ea -eb -mnet1 -[RHS]mnetD.
  apply: eq_mnet => f; rewrite !inE.
  by case: eqP => [->|_]; rewrite ?(negbTE eX) ?addr0 ?add0r.
exists e, (X :\ e); first exact: subset_trans (subD1set X e) XA.
split=> [f||v].
- by rewrite !inE; case: eqP => [->|_]; rewrite ?eX ?addbF.
- by rewrite ea eb !eqxx orbT.
rewrite -addrA (eq_sym v a) (eq_sym v b) -ea -eb -opprB -mnet1 -mnetN -[RHS]mnetD.
apply: eq_mnet => f; rewrite !inE; case: eqP => [->|_]; last by rewrite subr0.
by rewrite eX subrr.
Qed.

(** Toggling the edges of a residual path moves one unit of net outflow from its last vertex to
    its first one. *)
Local Lemma res_path_toggle X u p : X \subset A -> path (res_step X) u p -> uniq (u :: p) ->
  exists2 X' : {set edge G}, X' \subset A &
    forall v, mnet (ind X') v = mnet (ind X) v + (v == u)%:R - (v == last u p)%:R.
Proof.
elim: p u X => [|w p IH] u X XA; first by move=> _ _; exists X => // v; rewrite addrK.
case/andP=> uw pth /andP[up uniqp].
have [e [X1 X1A [X1E eE netX1]]] := res_step_toggle XA uw.
have allp : all (predC1 u) (w :: p) by apply/allP => z zp; apply: contraNneq up => <-.
have sub : {in predC1 u &, subrel (res_step X) (res_step X1)}.
  move=> a b; rewrite !inE => au bu /existsP[f hf]; apply/existsP; exists f.
  have fe : f != e.
    apply: contraTneq hf => ->; move: eE; rewrite !negb_or !negb_and.
    by case/orP=> /andP[/eqP-> /eqP->];
      rewrite ![u == _]eq_sym (negbTE au) (negbTE bu) /= !orbT.
  by move: hf; rewrite !inE !X1E (negbTE fe) !addbF.
have pth1 := sub_in_path sub allp pth.
have [X' X'A netX'] := IH w X1 X1A pth1 uniqp.
by exists X' => // v; rewrite netX' netX1 /= subrK.
Qed.

(** The theorem: demands [d] summing to 0, such that no set [S] demands more than the number of
    edges of [A] leaving it, are the net outflows of a set of edges of [A]. *)
Theorem demand_edge_set (d : G -> int) :
  \sum_v d v = 0 ->
  (forall S,
     \sum_(v in S) d v <= #|[set e in A | (source e \in S) && (target e \notin S)]|%:R) ->
  exists2 X : {set edge G}, X \subset A & forall v, mnet (ind X) v = d v.
Proof.
move=> d0 dcut; pose r X v := mnet (ind X) v - d v.
pose phi X := (\sum_v `|r X v|)%N.
case: (@arg_minnP _ set0 (fun X : {set edge G} => X \subset A) phi (sub0set A)) => X XA Xmin.
exists X => // v.
suff r0 v0 : 0 <= r X v0.
  have h0 : \sum_v r X v = 0 by rewrite /r sumrB sum_mnetT d0 subrr.
  by have /eqP := psumr_eq0P (fun v _ => r0 v) h0 (i := v) isT; rewrite subr_eq0 => /eqP.
(* Otherwise [v0] has a deficit. *)
rewrite leNgt; apply/negP => v0lt.
pose S := [set w | connect (res_step X) v0 w].
have [w /andP[wS wgt]|nogt] := pickP (fun w => (w \in S) && (0 < r X w)).
  (* A residual path from [v0] to a vertex [w] with a surplus: toggling it decreases [phi]. *)
  rewrite inE in wS; case/connectP: wS => p0 pth0 wl.
  case: (shortenP pth0) wl => p pth uniqp _ wl.
  have [X' X'A netX'] := res_path_toggle XA pth uniqp; rewrite -wl in netX'.
  have wv0 : w != v0 by apply: contraTneq wgt => ->; rewrite -leNgt ltW.
  have rX' z : r X' z = r X z + (z == v0)%:R - (z == w)%:R.
    by rewrite /r netX' addrAC; congr (_ - _); rewrite addrAC.
  have := Xmin X' X'A; rewrite leqNgt => /negP; apply.
  rewrite /phi (bigD1 v0) //= [in X in (_ < X)%N](bigD1 v0) //= -addSn; apply: leq_add.
    rewrite rX' eqxx eq_sym (negbTE wv0) subr0.
    case: (r X v0) v0lt => // n _.
    by rewrite NegzE abszN -[n.+1]addn1 PoszD opprD subrK abszN /= addn1.
  apply: leq_sum => z zv0; rewrite rX' (negbTE zv0) addr0.
  case: eqP => [->|_]; last by rewrite subr0.
  by case: (r X w) wgt => // -[|n] //= _; rewrite subn1 leq_pred.
(* Otherwise [S] is closed under residual steps: the edges of [A] leaving it are in [X], and no
   edge of [X] enters it, so the deviation over [S] is not negative. *)
have hcl a b : a \in S -> res_step X a b -> b \in S.
  by rewrite !inE => ha hab; apply: connect_trans ha (connect1 hab).
have v0S : v0 \in S by rewrite inE connect0.
have : \sum_(z in S) r X z < 0.
  rewrite (bigD1 v0) //= -(addr0 0) ltr_leD //; apply: sumr_le0 => z /andP[zS _].
  by move: (nogt z); rewrite /= zS /= => /negbT; rewrite -leNgt.
apply/negP; rewrite -leNgt /r sumrB sum_mnet subr_ge0; apply: le_trans (dcut S) _.
rewrite (@big1 _ _ _ _ _ (fun e => (target e \in S) && (source e \notin S))).
  move=> e /andP[tS sS]; case: (boolP (e \in X)) => // eX; move/negP: sS; case.
  by apply: (hcl _ _ tS); apply/existsP; exists e; rewrite eX !eqxx orbT.
rewrite subr0 -sum1_card natr_sum [X in X <= _]big_mkcond [X in _ <= X]big_mkcond /=.
apply: ler_sum => e _; rewrite inE.
case: (boolP ((source e \in S) && (target e \notin S))) => [/andP[sS tS]|_]; rewrite ?andbF //.
case: (boolP (e \in A)) => [eA|_]; rewrite ?ler0n //; case: (boolP (e \in X)) => // eX.
move/negP: tS; case; apply: (hcl _ _ sS).
by apply/existsP; exists e; rewrite !inE eX eA !eqxx.
Qed.

End Hoffman.

(** ** Tutte's theorem: Z_k-flows lift to integer flows *)

Section Tutte.
Variable G : mgraph.

(** A function whose net outflows are multiples of [k] is congruent modulo [k] to a flow whose
    values have absolute value less than [k]: with [r = f mod k], a set [X] of edges where
    [r != 0] such that [r - k [X]] is conservative exists by [demand_edge_set], as the net
    outflow of [r / k] from a set [S] is at most [(k-1)/k] times the number of these edges
    leaving [S]. *)
Theorem mod_flow_lift (k : nat) (f : edge G -> int) :
  (0 < k)%N -> (forall v, (k %| mnet f v)%Z) ->
  exists h : edge G -> int, conservative h /\ forall e, (k %| h e - f e)%Z /\ `|h e| < k%:R.
Proof.
move=> k0 fk; have k0' : (0 : int) < k%:R by rewrite ltr0n.
pose r e := (f e %% k)%Z; pose A := [set e | r e != 0].
have r0 e : 0 <= r e by apply: modz_ge0; case: (k) k0.
have rk e : r e < k%:R by rewrite natz; apply: ltz_pmod; rewrite -natz.
have rk' v : (k %| mnet r v)%Z.
  have -> : mnet r v = mnet f v - k%:R * mnet (fun e => (f e %/ k)%Z) v.
    rewrite -mnetZ -mnetN -mnetD; apply: eq_mnet => e.
    by rewrite /r {2}(divz_eq (f e) k) mulrC natz addrAC subrr add0r.
  by apply: rpredB; [exact: fk | rewrite natz; apply: dvdz_mulr; apply: dvdzz].
pose d v := (mnet r v %/ k)%Z.
have dk v : d v * k%:R = mnet r v by rewrite natz; apply: divzK.
have [X XA hX] : exists2 X : {set edge G},
    X \subset A & forall v, mnet (fun e => (e \in X)%:R : int) v = d v.
  apply: demand_edge_set => [|S].
    apply: (mulIf (lt0r_neq0 k0')); rewrite mul0r mulr_suml.
    by rewrite (eq_bigr _ (fun v _ => dk v)) sum_mnetT.
  rewrite -(ler_pM2r k0') mulr_suml (eq_bigr _ (fun v _ => dk v)) sum_mnet.
  apply: le_trans (_ : _ <= \sum_(e | (source e \in S) && (target e \notin S)) r e) _.
    by rewrite gerBl sumr_ge0.
  rewrite -sum1_card natr_sum mulr_suml [X in _ <= X]big_mkcond [X in X <= _]big_mkcond /=.
  apply: ler_sum => e _; rewrite !inE.
  case: (_ && _); rewrite ?andbT ?andbF // mul1r.
  by case: eqP => [->|_] //; apply: ltW.
exists (fun e => r e - k%:R * (e \in X)%:R); split => [|e].
  by apply/conservativeE => v; rewrite mnetD mnetN mnetZ hX -dk mulrC subrr.
split.
  rewrite addrAC; apply: rpredB; last by rewrite natz; apply: dvdz_mulr; apply: dvdzz.
  rewrite /r {2}(divz_eq (f e) k) opprD addrC -addrA addNr addr0.
  by rewrite rpredN; apply: dvdz_mull; apply: dvdzz.
case: (boolP (e \in X)) => [eX|_]; last by rewrite mulr0 subr0 ger0_norm.
have : r e != 0 by move/subsetP: XA => /(_ e eX); rewrite inE.
rewrite mulr1 ler0_norm ?subr_le0 ?(ltW (rk e)) // opprB => re0.
by rewrite gtrBl lt0r re0 r0.
Qed.

(** A nowhere-zero Z_k-flow gives a nowhere-zero [k]-flow. *)
Corollary mod_flow_nowhere_zero (k : nat) (f : edge G -> int) :
  (0 < k)%N -> (forall v, (k %| mnet f v)%Z) -> (forall e, ~~ (k %| f e)%Z) ->
  nowhere_zero_flow G k.
Proof.
move=> k0 fk fnz; have [h [hc hb]] := mod_flow_lift k0 fk; exists h; split=> // e.
have [hf hk] := hb e; split; last by rewrite -ltzD1 natr1 prednK.
rewrite -[1]add0r lezD1 normr_gt0; apply: contraNneq (fnz e) => h0.
by move: hf; rewrite h0 sub0r rpredN.
Qed.

End Tutte.

(** ** Rounding rational flows *)

Section Round.
Variable G : mgraph.

(** A rational flow whose values lie within [eps] of the intervals [[l e, l e + 1]], where
    [m eps < 1] for the number [m] of edges, gives an integer flow [l + [X]].  The demands
    [- mnet l] meet the cut condition of [demand_edge_set]: over a cut, the flow balances, so the
    deviation is at most [m eps < 1], hence at most 0 since it is an integer. *)
Theorem rat_flow_round (phi : edge G -> rat) (l : edge G -> int) (eps : rat) :
  conservative phi -> 0 <= eps -> #|edge G|%:R * eps < 1 ->
  (forall e, (l e)%:~R - eps <= phi e /\ phi e <= (l e)%:~R + 1 + eps) ->
  exists X : {set edge G}, conservative (fun e => l e + (e \in X)%:R).
Proof.
move=> hc eps0 meps hl.
have [X _ hX] : exists2 X : {set edge G}, X \subset [set: edge G] &
    forall v, mnet (fun e => (e \in X)%:R : int) v = - mnet l v.
  apply: demand_edge_set => [|S]; first by rewrite sumrN sum_mnetT oppr0.
  rewrite sumrN sum_mnet opprB.
  pose L e := (source e \in S) && (target e \notin S).
  pose E e := (target e \in S) && (source e \notin S).
  pose g e : rat := (if E e then (l e)%:~R - phi e else 0)
                    + (if L e then phi e - (l e)%:~R - 1 else 0).
  have gle e : g e <= eps.
    rewrite /g; have [h1 h2] := hl e.
    case: (boolP (E e)) => [/andP[tS sS]|_]; case: (boolP (L e)) => [/andP[sS' tS']|_].
    - by move: sS; rewrite sS'.
    - by rewrite addr0 lerBlDl -lerBlDr.
    - by rewrite add0r !lerBlDr (addrC eps) addrC addrA.
    - by rewrite addr0.
  have g1 : \sum_e g e < 1.
    apply: le_lt_trans meps; apply: le_trans (ler_sum _ (fun e _ => gle e)) _.
    by rewrite sumr_const mulr_natl.
  rewrite -subr_le0 -ltzD1 add0r -(ltr_int rat); apply: le_lt_trans g1.
  rewrite le_eqVlt; apply/orP; left; apply/eqP.
  have phi0 : \sum_(e | L e) phi e - \sum_(e | E e) phi e = 0.
    by rewrite -[LHS]sum_mnet big1 // => v _; move/conservativeE: hc.
  have cardL : #|[set e in [set: edge G] | L e]|%:R = \sum_(e | L e) (1 : int).
    by rewrite -sum1_card natr_sum; apply: eq_bigl => e; rewrite !inE.
  rewrite /g big_split /= -!big_mkcond /= !sumrB cardL rmorphB rmorphB /= !rmorph_sum /=.
  by move/eqP: phi0; rewrite subr_eq0 => /eqP ->; rewrite addrA addrA subrK.
by exists X; apply/conservativeE => v; rewrite mnetD hX subrr.
Qed.

(** A rational flow whose absolute values lie between [a] and [a + 1 + eps], with [m eps < 1],
    gives an integer flow whose absolute values lie between [a] and [a + 1]. *)
Corollary rat_flow_round_abs (phi : edge G -> rat) (a : nat) (eps : rat) :
  conservative phi -> 0 <= eps -> #|edge G|%:R * eps < 1 ->
  (forall e, a%:R <= `|phi e| <= a%:R + 1 + eps) ->
  exists g : edge G -> int, conservative g /\ forall e, a%:R <= `|g e| <= a.+1%:R.
Proof.
move=> hc eps0 meps hb.
pose l e : int := if 0 < phi e then a%:R else - a.+1%:R.
have [|X hX] := rat_flow_round hc eps0 meps (l := l).
  move=> e; have /andP[lo hi] := hb e; rewrite /l; case: ifP => [/gtr0_norm pe|/negbT].
    rewrite pe in lo hi; rewrite rmorph_nat; split=> //.
    by apply: le_trans lo; rewrite gerDl oppr_le0.
  rewrite -leNgt => /ler0_norm pe; rewrite pe in lo hi; rewrite rmorphN rmorph_nat.
  split; first by rewrite -opprD lerNl -natr1.
  by rewrite -natr1 opprD subrK (le_trans _ (_ : - a%:R <= _)) ?lerDl // lerNr.
exists (fun e => l e + (e \in X)%:R); split => // e; rewrite /l; case: ifP => _.
  by case: (e \in X); rewrite /= ?addr0 ?natr1 normr_nat ?lexx ler_nat ?leqnSn.
case: (e \in X); rewrite /= ?addr0 ?normrN ?normr_nat ?lexx ?ler_nat ?leqnSn //.
by rewrite -natr1 opprD subrK normrN normr_nat lexx lerDl.
Qed.

End Round.

(** ** Degrees and cuts *)

Section Degrees.
Variable G : mgraph.

(** In a loopless graph, the number of edges at [v] is its degree. *)
Lemma mloopless_edges_at (v : G) : mloopless G -> #|edges_at v| = mdeg v.
Proof. by move=> ll; rewrite /mdeg mdeg_in_loopless // setTI. Qed.

(** In a loopless [r]-regular graph, the parity of a cut is that of [r] times its side. *)
Lemma mregular_mcut_odd (r : nat) (X : {set G}) :
  mloopless G -> mregular G r -> odd #|mcut X| = odd (r * #|X|).
Proof.
move=> ll reg; rewrite -[mcut X]setTI -odd_mdeg_sum (eq_bigr (fun _ => r)) => [v _|].
  by rewrite -/(mdeg v) -mloopless_edges_at.
by rewrite sum_nat_const mulnC.
Qed.

(** In a [k]-edge-connected graph, every cut separating two vertices has at least [k] edges. *)
Lemma medge_connected_mcut k (S : {set G}) (x y : G) :
  medge_connected G k -> x \in S -> y \notin S -> (k <= #|mcut S|)%N.
Proof.
move=> hk xS yS; rewrite leqNgt; apply/negP => /hk /connectedTE /(_ x y) cxy.
suff cl : closed (@edge_rel (skeleton.skeleton (remove_edges (mcut S)))) (mem S).
  by have := closed_connect cl cxy; rewrite xS (negbTE yS).
move=> a b /andP[_ /existsP[e]]; have := valP e; rewrite !inE negb_add => /eqP est.
by case/orP=> /andP[/eqP<- /eqP<-].
Qed.

End Degrees.

(** ** Multiplying the edges *)

Section Multiply.
Variables (G : mgraph) (c : nat).

(** [G] with every edge replaced by [c] parallel edges. *)
Definition medge_mult : mgraph :=
  @Graph unit unit G (edge G * 'I_c)%type (fun b f => endpoint b f.1)
    (fun _ => tt) (fun _ => tt).

Lemma medge_mult_edges_at (v : G) : #|@edges_at _ _ medge_mult v| = (#|edges_at v| * c)%N.
Proof.
have -> : @edges_at _ _ medge_mult v = setX (edges_at v) [set: 'I_c].
  by apply/setP => -[e i]; rewrite !inE andbT.
by rewrite cardsX cardsT card_ord.
Qed.

Lemma medge_mult_mcut (S : {set G}) : #|@mcut medge_mult S| = (#|mcut S| * c)%N.
Proof.
have -> : @mcut medge_mult S = setX (mcut S) [set: 'I_c].
  by apply/setP => -[e i]; rewrite !inE andbT.
by rewrite cardsX cardsT card_ord.
Qed.

(** Summing over the copies of each edge preserves the net outflows. *)
Lemma medge_mult_mnet (h : edge medge_mult -> int) (v : G) :
  mnet (fun e => \sum_(i < c) h (e, i)) v = @mnet medge_mult _ h v.
Proof.
rewrite /mnet !pair_big_dep /=.
by congr (_ - _); apply: eq_big => [[e i]|[e i] _] /=; rewrite ?andbT.
Qed.

End Multiply.

(** ** Reduction to graphs whose separating cuts have at least three edges *)

Section Identify.
Variables (G : mgraph) (u w : G).
Hypothesis uw : u != w.

Local Definition ident_proj (v : G) : G := if v == w then u else v.

Local Lemma ident_proj_neq v : ident_proj v != w.
Proof. by rewrite /ident_proj; case: ifP => // /negbT. Qed.

(** [G] with [w] identified with [u]: the vertices other than [w], and the same edges. *)
Definition ident_graph : mgraph :=
  @Graph unit unit {v : G | v != w} (edge G)
    (fun b e => Sub (ident_proj (endpoint b e)) (ident_proj_neq _)) (fun _ => tt) (fun _ => tt).

Lemma ident_card : (#|ident_graph| < #|G|)%N.
Proof.
rewrite /= card_sig (eq_card (B := predC1 w)) // cardC1 prednK //.
by apply/card_gt0P; exists w.
Qed.

Local Lemma ident_uwalk x y p : uwalk x y p ->
  @uwalk ident_graph (Sub (ident_proj x) (ident_proj_neq x))
    (Sub (ident_proj y) (ident_proj_neq y)) p.
Proof.
elim: p x => [|f p IH] x /=; first by move=> /eqP->; rewrite eqxx.
by case/orP=> /andP[/eqP<- hp]; rewrite eqxx (IH _ hp) ?orbT.
Qed.

Lemma ident_bridgeless : bridgeless G -> bridgeless ident_graph.
Proof. by move=> hbl e hbr; apply: (hbl e) => p /ident_uwalk; apply: hbr. Qed.

(** A flow of the identified graph is conservative at the vertices of [G] other than [u] and
    [w], and the net outflows at [u] and [w] cancel. *)
Lemma ident_conservative (phi : edge G -> int) : conservative (G := ident_graph) phi ->
  (forall v, v != u -> v != w -> mnet phi v = 0) /\ mnet phi u + mnet phi w = 0.
Proof.
move=> /conservativeE hc.
have hv v (vw : v != w) : mnet phi v + (v == u)%:R * mnet phi w = 0.
  rewrite -(hc (Sub v vw)) /mnet.
  have hs b : \sum_(e | @endpoint _ _ ident_graph b e == Sub v vw) phi e
      = \sum_(e | endpoint b e == v) phi e + (v == u)%:R * \sum_(e | endpoint b e == w) phi e.
    rewrite mulr_sumr !(big_mkcond (fun e => _ == _)) -big_split; apply: eq_bigr => e _ /=.
    rewrite -val_eqE !SubK /ident_proj.
    case: (@endpoint _ _ G b e =P w) => [->|_]; last by rewrite addr0.
    by rewrite (eq_sym w) (negbTE vw) add0r eq_sym; case: eqP; rewrite ?mul1r ?mul0r.
  by rewrite (hs false) (hs true) opprD addrACA -mulrBr.
split=> [v vu vw|]; first by have := hv v vw; rewrite (negbTE vu) mul0r addr0.
by have := hv u uw; rewrite eqxx mul1r.
Qed.

End Identify.

(** If every graph whose separating cuts have at least 3 edges has a nowhere-zero [k]-flow, then
    every bridgeless graph has one.  By induction on the number of vertices: a cut [S] with fewer
    than 3 edges has 0 or 2 of them ([bridgeless_mcut1]).  Identify a vertex [w] outside [S] with
    a vertex [u] in [S], the ends of an edge [e] of the cut if it has two edges [e] and [f].  The
    identified graph is bridgeless.  Its flow is a flow of [G] except at [u] and [w], where the
    net outflows cancel; summed over [S], they count the cut.  If the cut is empty, the flow is
    conservative; otherwise correcting the value of [e] makes it conservative, and its absolute
    value becomes that of [f]. *)
Theorem nowhere_zero_flow_reduction (k : nat) :
  (forall G : mgraph, (0 < #|edge G|)%N ->
     (forall (S : {set G}) x y, x \in S -> y \notin S -> (3 <= #|mcut S|)%N) ->
     nowhere_zero_flow G k) ->
  forall G : mgraph, (0 < #|edge G|)%N -> bridgeless G -> nowhere_zero_flow G k.
Proof.
move=> h3 G; move: {2}#|G| (leqnn #|G|) => n; elim: n G => [|n IH] G Gn E0 hbl.
  by case/card_gt0P: E0 => e _; move: Gn; rewrite leqn0 => /eqP/card0_eq/(_ (source e)).
have [all3|] := boolP [forall S : {set G}, forall x, forall y,
                         (x \in S) ==> (y \in S) || (3 <= #|mcut S|)%N].
  apply: h3 => // S x y xS yS; move/forallP/(_ S)/forallP/(_ x)/forallP/(_ y): all3.
  by rewrite xS (negbTE yS).
rewrite negb_forall => /existsP[S]; rewrite negb_forall => /existsP[x].
rewrite negb_forall => /existsP[y]; rewrite negb_imply negb_or -ltnNge => /and3P[xS yS lt3].
pose sgn (g : edge G) : int := (source g \in S)%:R - (target g \in S)%:R.
have sgn0 g : g \notin mcut S -> sgn g = 0 by rewrite /sgn inE negb_add => /eqP->; rewrite subrr.
(* Identify [w] outside [S] with [u] in [S]. *)
have step u w : u \in S -> w \notin S -> exists phi : edge G -> int,
    [/\ nowhere_zero_bounded k phi, forall v, v != u -> v != w -> mnet phi v = 0,
        mnet phi u + mnet phi w = 0 & mnet phi u = \sum_g phi g * sgn g].
  move=> uS wS; have uw : u != w by apply: contraNneq wS => <-.
  have Gn' : (#|ident_graph uw| <= n)%N by rewrite -ltnS (leq_trans (ident_card uw)).
  have [phi [hc hb]] := IH _ Gn' E0 (ident_bridgeless (uw := uw) hbl).
  have [h0 huw] := ident_conservative hc.
  exists phi; split => //; rewrite -sum_mnet_sign (bigD1 u) //= big1 ?addr0 //.
  move=> v /andP[vS vu].
  by apply: h0 => //; apply: contraNneq wS => <-.
have [c0|/set0Pn[e ec]] := eqVneq (mcut S) set0.
  (* An empty cut. *)
  have [phi [hb h0 hxy hx]] := step x y xS yS.
  exists phi; split => //; apply/conservativeE => v.
  have hx0 : mnet phi x = 0 by rewrite hx big1 // => g _; rewrite sgn0 ?mulr0 // c0 inE.
  case: (eqVneq v x) => [->//|vx]; case: (eqVneq v y) => [->|vy]; last exact: h0.
  by move: hxy; rewrite hx0 add0r.
(* A cut with two edges [e] and [f]. *)
have [f fe cutS] : exists2 f, f != e & mcut S = [set e; f].
  move: lt3 (bridgeless_mcut hbl ec); rewrite (cardsD1 e) ec.
  case/boolP: (#|mcut S :\ e| == 1%N) => [/cards1P[f fS] _ _|].
    2: by case: #|_| => [|[|[]]].
  exists f; first by have := set11 f; rewrite -fS !inE => /andP[].
  by rewrite -(setD1K ec) fS.
have [u [w [uS wS ends]]] : exists u w, [/\ u \in S, w \notin S &
    ((source e == u) && (target e == w)) || ((source e == w) && (target e == u))].
  move: ec; rewrite inE; case sS: (source e \in S) => /= tS.
    by exists (source e), (target e); rewrite sS tS !eqxx.
  by exists (target e), (source e); rewrite sS tS !eqxx orbT.
have [phi [hb h0 huw hu]] := step u w uS wS.
pose s : int := (source e == u)%:R - (target e == u)%:R.
pose psi g := phi g - s * mnet phi u * (g == e)%:R.
have mpsi v :
    mnet psi v = mnet phi v - s * mnet phi u * ((source e == v)%:R - (target e == v)%:R).
  by rewrite mnetD mnetN mnetZ mnet1.
have uw : (w == u) = false by apply/negbTE; apply: contraNneq wS => ->.
have [ss sw] : s * s = 1 /\ (source e == w)%:R - (target e == w)%:R = - s.
  by rewrite /s; case/orP: ends => /andP[/eqP-> /eqP->]; rewrite !eqxx uw eq_sym uw.
have cpsi : forall v, mnet psi v = 0.
  move=> v; rewrite mpsi; case: (eqVneq v u) => [->|vu].
    by rewrite -/s mulrAC ss mul1r subrr.
  case: (eqVneq v w) => [->|vw]; first by rewrite sw mulrN opprK mulrAC ss mul1r addrC.
  have -> : (source e == v)%:R - (target e == v)%:R = 0 :> int.
    by case/orP: ends => /andP[/eqP-> /eqP->]; rewrite ![_ == v]eq_sym (negbTE vu) (negbTE vw).
  by rewrite mulr0 subr0 h0.
exists psi; split; first exact/conservativeE.
have psif : psi f = phi f by rewrite /psi (negbTE fe) mulr0 subr0.
move=> g; case: (eqVneq g e) => [->|ge].
  2: by rewrite /psi (negbTE ge) mulr0 subr0; apply: hb.
suff -> : `|psi e| = `|phi f| by apply: hb.
have sgn1 h : h \in mcut S -> `|sgn h| = 1.
  by rewrite /sgn inE; case: (source h \in S); case: (target h \in S); rewrite ?normrN ?normr1.
have := sum_mnet_sign psi S; rewrite big1 => [v _|]; first exact: cpsi.
rewrite (bigD1 e) ?cutS ?set21 //= (bigD1 f) ?inE ?eqxx ?orbT ?fe //= big1 ?addr0.
  by move=> h /andP[he hf]; rewrite -/(sgn h) sgn0 ?mulr0 // cutS !inE negb_or he.
move/esym/eqP; rewrite addr_eq0 => /eqP /(congr1 Num.norm).
by rewrite normrN !normrM -/(sgn e) -/(sgn f) !sgn1 ?mulr1 ?psif // cutS !inE eqxx ?orbT.
Qed.

