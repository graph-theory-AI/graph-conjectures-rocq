(** * Chains over a ring

    For a finite type [cell] of cells and a ring [R], a chain is a finite function [cell -> R^o].
    This file adds to the module structure of MathComp the basis chains [cc x], the linear
    extension [lin f] of a map [f] defined on cells, and lemmas to reason cell by cell. *)

From mathcomp Require Import boot algebra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Local Open Scope ring_scope.

Section Chains.
Variables (R : nzRingType) (cell : finType).

Local Abbreviation chain := ({ffun cell -> R^o}).

(** The basis chain of a cell. *)
Definition cc (x : cell) : chain := [ffun y => (y == x)%:R].

Lemma ccE x y : cc x y = (y == x)%:R.
Proof. by rewrite ffunE. Qed.

Lemma chain_decomp (c : chain) : c = \sum_(x : cell) c x *: cc x.
Proof.
apply/ffunP => y; rewrite sum_ffunE (bigD1 y) //= !ffunE eqxx.
rewrite /GRing.scale /= mulr1 big1 ?addr0 // => x /negbTE neq.
by rewrite /ffun_scale !ffunE /GRing.scale /= eq_sym neq mulr0.
Qed.

Section Lin.
Variable (cell' : finType).

(** Linear extension of a map defined on cells. *)
Definition lin (f : cell -> {ffun cell' -> R^o}) (c : chain) : {ffun cell' -> R^o} :=
  \sum_(x : cell) c x *: f x.

Variable (f : cell -> {ffun cell' -> R^o}).

Lemma lin_cc x : lin f (cc x) = f x.
Proof.
rewrite /lin (bigD1 x) //= ffunE eqxx scale1r big1 ?addr0 // => y /negbTE neq.
by rewrite ffunE neq scale0r.
Qed.

Lemma linD c1 c2 : lin f (c1 + c2) = lin f c1 + lin f c2.
Proof.
by rewrite /lin -big_split; apply: eq_bigr => x _; rewrite ffunE scalerDl.
Qed.

Lemma linZ a c : lin f (a *: c) = a *: lin f c.
Proof.
by rewrite /lin scaler_sumr; apply: eq_bigr => x _; rewrite ffunE scalerA.
Qed.

Lemma linN c : lin f (- c) = - lin f c.
Proof. by rewrite -scaleN1r linZ scaleN1r. Qed.

Lemma linB c1 c2 : lin f (c1 - c2) = lin f c1 - lin f c2.
Proof. by rewrite linD linN. Qed.

Lemma lin0 : lin f 0 = 0.
Proof. by rewrite -(scale0r 0) linZ scale0r. Qed.

Lemma lin_sum (I : Type) (r : seq I) (F : I -> chain) :
  lin f (\sum_(i <- r) F i) = \sum_(i <- r) lin f (F i).
Proof. by elim/big_rec2: _ => [|i c1 c2 _ <-]; rewrite ?lin0 ?linD. Qed.

Lemma linE c : lin f c = \sum_(x : cell) c x *: f x.
Proof. by []. Qed.

End Lin.

(** Two maps that are additive, homogeneous and agree on cells agree everywhere. *)
Lemma chain_ext (cell' : finType) (F G : chain -> {ffun cell' -> R^o}) :
  (forall c1 c2, F (c1 + c2) = F c1 + F c2) ->
  (forall a c, F (a *: c) = a *: F c) ->
  (forall c1 c2, G (c1 + c2) = G c1 + G c2) ->
  (forall a c, G (a *: c) = a *: G c) ->
  (forall x, F (cc x) = G (cc x)) -> forall c, F c = G c.
Proof.
move=> FD FZ GD GZ FG c; rewrite [c]chain_decomp.
have sumF : forall (r : seq cell) (H : cell -> chain),
    F (\sum_(x <- r) H x) = \sum_(x <- r) F (H x).
  move=> r H; elim/big_rec2: _ => [|x c1 c2 _ <-]; last by rewrite FD.
  by rewrite -(scale0r 0) FZ scale0r.
have sumG : forall (r : seq cell) (H : cell -> chain),
    G (\sum_(x <- r) H x) = \sum_(x <- r) G (H x).
  move=> r H; elim/big_rec2: _ => [|x c1 c2 _ <-]; last by rewrite GD.
  by rewrite -(scale0r 0) GZ scale0r.
by rewrite sumF sumG; apply: eq_bigr => x _; rewrite FZ GZ FG.
Qed.

End Chains.

(** A double sum of an antisymmetric family vanishes — over ANY ring (the
    pairing is term-by-term, so this does not divide by 2).  [rnk] supplies a
    total order on the index type. *)
Lemma sum_pair_anti (I : finType) (M : zmodType) (rnk : I -> nat)
    (F : I -> I -> M) :
  injective rnk ->
  (forall i, F i i = 0) -> (forall i j, F i j = - F j i) ->
  \sum_(i : I) \sum_(j : I) F i j = 0.
Proof.
move=> rnk_inj Fdiag Fanti.
rewrite pair_big /=.
rewrite (bigID (fun q : I * I => (rnk q.2 < rnk q.1)%N)) /=.
rewrite [X in _ + X](reindex_inj (h := fun q : I * I => (q.2, q.1)));
  first [by move=> [a b] [a' b'] [] -> -> | idtac].
rewrite [X in _ + X](eq_bigr (fun q : I * I => - F q.1 q.2));
  first [by move=> q _ /=; rewrite Fanti | idtac].
rewrite [X in _ + X]sumrN.
apply/eqP; rewrite subr_eq0; apply/eqP.
rewrite [in RHS]big_mkcond [in LHS]big_mkcond; apply: eq_bigr => q _ /=.
case: (ltngtP (rnk q.2) (rnk q.1)) => h.
- by [].
- by [].
- by move/rnk_inj: h => ->; rewrite Fdiag.
Qed.

Arguments cc {R cell} x.
Arguments lin {R cell cell'} f c.

Lemma lin_comp (R : nzRingType) (cell cell' cell'' : finType) (f : cell -> {ffun cell' -> R^o})
    (g : cell' -> {ffun cell'' -> R^o}) (c : {ffun cell -> R^o}) :
  lin g (lin f c) = lin (fun x => lin g (f x)) c.
Proof.
rewrite [lin f c]linE lin_sum; apply: eq_bigr => x _.
by rewrite linZ.
Qed.

Lemma scale_ffunE (R : nzRingType) (cell : finType) (a : R)
    (f : {ffun cell -> R^o}) (x : cell) : (a *: f) x = a * f x.
Proof. by rewrite ffunE. Qed.

(** Two linear extensions agreeing on the support of a chain agree on it. *)
Lemma lin_eq_supp (R : nzRingType) (cell cell' : finType)
    (f g : cell -> {ffun cell' -> R^o}) (c : {ffun cell -> R^o}) :
  (forall x, c x != 0 -> f x = g x) -> lin f c = lin g c.
Proof.
move=> h; rewrite /lin; apply: eq_bigr => x _.
by case: (altP (c x =P 0)) => [->|hx]; rewrite ?scale0r ?h.
Qed.

(** A chain supported on a single cell is a multiple of its basis chain. *)
Lemma chain_supp1 (R : nzRingType) (cell : finType)
    (z : {ffun cell -> R^o}) (x : cell) :
  (forall y, z y != 0 -> y = x) -> z = z x *: cc x.
Proof.
move=> h; apply/ffunP => y; rewrite scale_ffunE ccE.
case: (eqVneq y x) => [->|yx]; first by rewrite mulr1.
rewrite mulr0; apply/eqP; apply: contraT => hy.
by move: (h y hy) => e; rewrite e eqxx in yx.
Qed.

(** [lin f] commutes with a filtered sum. *)
Lemma lin_sum_cond (R : nzRingType) (cell cell' I : finType)
    (f : cell -> {ffun cell' -> R^o}) (P : pred I) (F : I -> {ffun cell -> R^o}) :
  lin f (\sum_(i | P i) F i) = \sum_(i | P i) lin f (F i).
Proof.
rewrite big_mkcond lin_sum [RHS]big_mkcond.
by apply: eq_bigr => i _; case: (P i); rewrite ?lin0.
Qed.

Lemma lin_cc_id (R : nzRingType) (cell : finType) (c : {ffun cell -> R^o}) :
  lin cc c = c.
Proof. by rewrite /lin -chain_decomp. Qed.

(** augmentation of a basis chain and of a combination of basis chains *)
Lemma sum_cc_aug (R : nzRingType) (cell : finType) (x : cell) :
  \sum_(y : cell) (cc x : {ffun cell -> R^o}) y = 1.
Proof.
by rewrite (bigD1 x) //= ccE eqxx big1 ?addr0 // => y h; rewrite ccE (negbTE h).
Qed.

Lemma aug_bigsum (R : nzRingType) (cell I : finType) (P : pred I)
    (F : I -> cell) (b : I -> R) :
  \sum_(y : cell) ((\sum_(i | P i) b i *: cc (F i)) : {ffun cell -> R^o}) y
  = \sum_(i | P i) b i.
Proof.
rewrite (eq_bigr (fun y => \sum_(i | P i) (b i *: (cc (F i) : {ffun cell -> R^o})) y));
  first [by move=> y _; rewrite sum_ffunE | idtac].
rewrite exchange_big /=; apply: eq_bigr => i _.
rewrite (eq_bigr (fun y => b i * (cc (F i) : {ffun cell -> R^o}) y));
  first [by move=> y _; rewrite scale_ffunE | idtac].
by rewrite -mulr_sumr sum_cc_aug mulr1.
Qed.

(** a cell in the support of a sum is in the support of one summand *)
Lemma supp_bigsum (R : nzRingType) (cell I : finType) (P : pred I)
    (F : I -> {ffun cell -> R^o}) (c : cell) :
  ((\sum_(i | P i) F i) c != 0) -> exists2 i, P i & (F i) c != 0.
Proof.
move=> h; case: (boolP [exists i, P i && (F i c != 0)]).
  by move=> /existsP[i /andP[hi hc]]; exists i.
move/existsPn => hno; exfalso; move/eqP: h; apply.
rewrite sum_ffunE big1 // => i hi.
by apply/eqP; move: (hno i); rewrite negb_and hi /= negbK.
Qed.

Lemma aug_lin (R : nzRingType) (cell cell' : finType)
    (f : cell -> {ffun cell' -> R^o}) (x : {ffun cell -> R^o}) :
  \sum_(y : cell') (lin f x) y = \sum_(c : cell) x c * (\sum_(y : cell') (f c) y).
Proof.
rewrite /lin (eq_bigr (fun y => \sum_(c : cell) (x c *: f c) y));
  first [by move=> y _; rewrite sum_ffunE | idtac].
rewrite exchange_big /=; apply: eq_bigr => c _.
rewrite mulr_sumr; apply: eq_bigr => y _.
by rewrite scale_ffunE.
Qed.
