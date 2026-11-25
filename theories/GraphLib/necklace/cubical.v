(** * The cubical chain complex of a power of a star

    R is the star with centre [o] and [p] paths of length [n].  A cell of one factor ([cell1]) is a
    vertex [Vtx v] or an edge [Edg k r], the edge of path [r] between [Some (k, r)] and its
    [slide].  A cell of R^N is a function [cellN := {ffun 'I_N -> cell1}], whose dimension is the
    number of coordinates that are edges.  The boundary [bd] is the sum over these coordinates,
    with alternating signs, of the difference between the two ends.  It satisfies [bd \o bd = 0]. *)

From mathcomp Require Import boot algebra.
From GC.GraphLib.necklace Require Import chains.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Local Open Scope ring_scope.

Section Cubical.
Variables (n p : nat).

Definition cut := option ('I_n * 'I_p).
Definition slide (x : cut) : cut :=
  if x is Some (k, r) then
    (if k == 0 :> nat then None
     else Some (Ordinal (leq_ltn_trans (leq_pred k) (ltn_ord k)), r))
  else None.

Definition cell1 := (cut + ('I_n * 'I_p))%type.
Definition Vtx (v : cut) : cell1 := inl v.
Definition Edg (kr : 'I_n * 'I_p) : cell1 := inr kr.
Definition is_edge (x : cell1) : bool := if x is inr _ then true else false.
Definition etop (kr : 'I_n * 'I_p) : cut := Some kr.
Definition ebot (kr : 'I_n * 'I_p) : cut := slide (Some kr).

Variable N : nat.
Definition cellN := {ffun 'I_N -> cell1}.

Definition dimN (c : cellN) : nat := #|[set j | is_edge (c j)]|.

(** Set coordinate [j] to the vertex [v]. *)
Definition fv (c : cellN) (j : 'I_N) (v : cut) : cellN :=
  [ffun i => if i == j then Vtx v else c i].

Definition rk (c : cellN) (j : 'I_N) : nat :=
  #|[set i : 'I_N | is_edge (c i) && (val i < val j)%N]|.

Section Ring.
Variable R : comNzRingType.

Definition edgeterm (c : cellN) (j : 'I_N) : {ffun cellN -> R^o} :=
  if c j is inr kr then
    (-1) ^+ (rk c j) *: (cc (fv c j (etop kr)) - cc (fv c j (ebot kr)))
  else 0.

Definition bd1 (c : cellN) : {ffun cellN -> R^o} := \sum_(j : 'I_N) edgeterm c j.
Definition bd : {ffun cellN -> R^o} -> {ffun cellN -> R^o} := lin bd1.

Lemma bdD x y : bd (x + y) = bd x + bd y. Proof. exact: linD. Qed.
Lemma bdZ a x : bd (a *: x) = a *: bd x. Proof. exact: linZ. Qed.
Lemma bd_cc c : bd (cc c) = bd1 c. Proof. exact: lin_cc. Qed.

(** ** Face calculus *)

Lemma fvE c j v i : fv c j v i = if i == j then Vtx v else c i.
Proof. by rewrite ffunE. Qed.

Lemma fv_same c j v : fv c j v j = Vtx v.
Proof. by rewrite fvE eqxx. Qed.

Lemma fvC c j v k w : j != k -> fv (fv c j v) k w = fv (fv c k w) j v.
Proof.
move=> jk; apply/ffunP => i; rewrite !fvE.
case: (eqVneq i k) => [->|_]; last by [].
by rewrite eq_sym (negbTE jk).
Qed.

Lemma is_edge_fv c j v i : is_edge (fv c j v i) = (i != j) && is_edge (c i).
Proof. by rewrite fvE; case: eqP. Qed.

Lemma edgeterm_novtx (c : cellN) j : ~~ is_edge (c j) -> edgeterm c j = 0 :> {ffun cellN -> R^o}.
Proof. by rewrite /edgeterm; case: (c j). Qed.

(** The rank of a coordinate [i] after coordinate [j] has been turned into a
    vertex: unchanged if [i] precedes [j], drops by one otherwise. *)
Lemma rk_fv (c : cellN) j v i : i != j -> is_edge (c j) ->
  rk (fv c j v) i = (rk c i - (val j < val i))%N.
Proof.
move=> ij ej; rewrite /rk.
have hset : [set i0 | is_edge (fv c j v i0) & (val i0 < val i)%N]
          = [set i0 in [set k | is_edge (c k) & (val k < val i)%N] | i0 != j].
  apply/setP => k; rewrite !inE is_edge_fv.
  by case: (is_edge (c k)); case: (val k < val i)%N; case: (k != j).
rewrite hset [in RHS](cardsD1 j) inE ej /=.
rewrite (cardsD1 j [set i0 in _ | i0 != j]) inE inE eqxx andbF add0n.
rewrite addKn.
apply: eq_card => k; rewrite !inE.
by case: (eqVneq k j) => [->|_]; rewrite ?andbF ?andbT.
Qed.

(** top/bottom vertices of a cell coordinate (dummy on vertex coordinates). *)
Definition tc (x : cell1) : cut := if x is inr kr then Some kr else None.
Definition bc (x : cell1) : cut := if x is inr kr then slide (Some kr) else None.

(** The four doubly-faced cells at distinct coordinates [j], [i]. *)
Definition quad (c : cellN) (j i : 'I_N) : {ffun cellN -> R^o} :=
  cc (fv (fv c j (tc (c j))) i (tc (c i)))
  - cc (fv (fv c j (tc (c j))) i (bc (c i)))
  - cc (fv (fv c j (bc (c j))) i (tc (c i)))
  + cc (fv (fv c j (bc (c j))) i (bc (c i))).

Definition coefT (c : cellN) (j i : 'I_N) : R :=
  (-1) ^+ (rk c j) * (-1) ^+ (rk c i - (val j < val i)).

Definition Tterm (c : cellN) (j i : 'I_N) : {ffun cellN -> R^o} :=
  if [&& is_edge (c j), is_edge (c i) & i != j]
  then coefT c j i *: quad c j i else 0.

(** Abstract antisymmetric-pairing lemma (valid over any ring, no /2). *)
Lemma sum_pair_anti (M : zmodType) (F : 'I_N -> 'I_N -> M) :
  (forall i, F i i = 0) -> (forall i j, F i j = - F j i) ->
  \sum_(j : 'I_N) \sum_(i : 'I_N) F j i = 0.
Proof.
move=> Fdiag Fanti.
rewrite pair_big /=.
rewrite (bigID (fun q : 'I_N * 'I_N => (val q.2 < val q.1)%N)) /=.
rewrite [X in _ + X](reindex_inj (h := fun q : 'I_N * 'I_N => (q.2, q.1)));
  first [by move=> [a b] [a' b'] [] -> -> | idtac].
rewrite [X in _ + X](eq_bigr (fun j : 'I_N*'I_N => - F j.1 j.2));
  first [by move=> q _ /=; rewrite Fanti | idtac].
rewrite [X in _ + X]sumrN.
apply/eqP; rewrite subr_eq0; apply/eqP.
rewrite [in RHS]big_mkcond [in LHS]big_mkcond; apply: eq_bigr => q _ /=.
case: (ltngtP (val q.2) (val q.1)) => h.
- by [].
- by [].
- by move/val_inj: h => ->; rewrite Fdiag.
Qed.

Lemma quadC (c : cellN) (j i : 'I_N) : i != j -> quad c j i = quad c i j.
Proof.
move=> ij; rewrite /quad.
rewrite [fv (fv c i (tc (c i))) j (tc (c j))](fvC _ _ _ ij) 1?eq_sym //.
rewrite [fv (fv c i (tc (c i))) j (bc (c j))](fvC _ _ _ ij) 1?eq_sym //.
rewrite [fv (fv c i (bc (c i))) j (tc (c j))](fvC _ _ _ ij) 1?eq_sym //.
rewrite [fv (fv c i (bc (c i))) j (bc (c j))](fvC _ _ _ ij) 1?eq_sym //.
by rewrite -!addrA; congr (_ + _); rewrite addrCA.
Qed.

Lemma coefT_anti (c : cellN) (j i : 'I_N) :
  is_edge (c j) -> is_edge (c i) -> i != j -> coefT c i j = - coefT c j i.
Proof.
move=> ej ei ij; rewrite /coefT.
have sgnB1 (m : nat) : (0 < m)%N -> (-1) ^+ (m - 1) = - ((-1) ^+ m) :> R.
  by case: m => // m _; rewrite subn1 /= exprS mulN1r opprK.
have rkpos (a b : 'I_N) : is_edge (c a) -> (val a < val b)%N -> (0 < rk c b)%N.
  by move=> ea hab; rewrite /rk (cardsD1 a) inE ea hab add1n.
case: (ltngtP (val i) (val j)) => [h|h|/val_inj/eqP]; last by rewrite (negbTE ij).
- by rewrite subn0 sgnB1 ?(rkpos i j) // mulrN mulrC.
- by rewrite subn0 sgnB1 ?(rkpos j i) // mulrN opprK mulrC.
Qed.

Lemma Tterm_diag (c : cellN) (j : 'I_N) : Tterm c j j = 0.
Proof. by rewrite /Tterm; case: ifP => // /and3P[_ _]; rewrite eqxx. Qed.

Lemma Tterm_anti (c : cellN) (j i : 'I_N) : Tterm c i j = - Tterm c j i.
Proof.
rewrite /Tterm; case: (eqVneq i j) => [->|ij]; first by rewrite !andbF oppr0.
rewrite ![~~ false]/= !andbT.
case Ej : (is_edge (c j)); last by rewrite andbF /= oppr0.
case Ei : (is_edge (c i)); last by rewrite andbF /= oppr0.
rewrite /= (coefT_anti Ej Ei ij) scaleNr quadC //.
by rewrite eq_sym.
Qed.

Lemma bd1_fv (c : cellN) j v : is_edge (c j) ->
  bd1 (fv c j v)
  = \sum_(i : 'I_N)
      (if is_edge (c i) && (i != j)
       then (-1) ^+ (rk c i - (val j < val i)) *:
            (cc (fv (fv c j v) i (tc (c i))) - cc (fv (fv c j v) i (bc (c i))))
       else 0).
Proof.
move=> ej; rewrite /bd1; apply: eq_bigr => i _; rewrite /edgeterm.
case: (eqVneq i j) => [->|ij].
  by rewrite fv_same andbF.
rewrite fvE (negbTE ij) andbT.
case E : (c i) => [v'|kr] //=.
rewrite (rk_fv v ij ej).
by rewrite /etop /ebot.
Qed.

Lemma bd_bd1 (c : cellN) : bd (bd1 c) = \sum_(j : 'I_N) \sum_(i : 'I_N) Tterm c j i.
Proof.
rewrite /bd /bd1 lin_sum; apply: eq_bigr => j _.
rewrite /edgeterm.
case Ej : (c j) => [v|kr].
  by rewrite lin0 big1 // => i _; rewrite /Tterm Ej.
rewrite linZ linB !lin_cc.
rewrite -/(bd1 (fv c j (etop kr))) -/(bd1 (fv c j (ebot kr))) !bd1_fv ?Ej //.
rewrite -sumrB scaler_sumr; apply: eq_bigr => i _.
rewrite /Tterm Ej /=.
case: (boolP (is_edge (c i) && (i != j))) => [hi|hi]; last first.
  by rewrite subrr scaler0.
case/andP: hi => ei ij.
rewrite -scalerBr scalerA /coefT; congr (_ *: _).
rewrite /quad.
have et : etop kr = tc (c j) by rewrite Ej.
have eb : ebot kr = bc (c j) by rewrite Ej.
rewrite et eb opprB.
by rewrite addrA addrAC.
Qed.

(** The keystone: [bd (bd x) = 0]. *)
Lemma bd_bd x : bd (bd x) = 0.
Proof.
have dd c : bd (bd1 c) = 0.
  rewrite bd_bd1 sum_pair_anti // => [i|i j]; [exact: Tterm_diag | exact: Tterm_anti].
rewrite {1}/bd lin_comp /lin big1 // => c _.
by rewrite -/(lin bd1 (bd1 c)) -/(bd (bd1 c)) dd scaler0.
Qed.

End Ring.
End Cubical.

(** Make the section parameters implicit for downstream use. *)
Arguments cut : clear implicits.
Arguments slide {n p} x.
Arguments cell1 : clear implicits.
Arguments Vtx {n p} v.
Arguments Edg {n p} kr.
Arguments is_edge {n p} x.
Arguments etop {n p} kr.
Arguments ebot {n p} kr.
Arguments tc {n p} x.
Arguments bc {n p} x.
Arguments cellN : clear implicits.
Arguments dimN {n p N} c.
Arguments fv {n p N} c j v.
Arguments rk {n p N} c j.
Arguments edgeterm {n p N R} c j.
Arguments bd1 {n p N R} c.
Arguments bd {n p N R} x.
Arguments bd_bd {n p N R} x.
Arguments bd1_fv {n p N R} c j v.
Arguments bd_cc {n p N R} c.
Arguments bdD {n p N R} x y.
Arguments bdZ {n p N R} a x.
Arguments fvE {n p N} c j v i.
Arguments fv_same {n p N} c j v.
Arguments fvC {n p N} c j v k w.
Arguments is_edge_fv {n p N} c j v i.
Arguments rk_fv {n p N} c j v i.
