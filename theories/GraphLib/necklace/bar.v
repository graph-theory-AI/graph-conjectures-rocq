(** * The homogeneous bar complex of Z_p

    The target of the chain map of eta.v is the homogeneous bar resolution of Z_p, on which the
    cochains of salt.v are defined; Meunier (2014) uses the join of copies of Z_p instead.  It is
    contractible, with the contraction that prepends the neutral element, so that an equivariant
    chain map to it is built by induction on the dimension, without subdivision nor connectivity
    argument.  A cell of dimension d is a sequence of d+1 elements of Z_p, of bounded length. *)

From mathcomp Require Import boot algebra.
From GC.GraphLib.necklace Require Import chains simplotope salt.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Set SsrOldRewriteGoalsOrder.
Local Open Scope ring_scope.

(** ** deleting one entry of a sequence *)

Section Dels.
Variable T : Type.

Definition dels (i : nat) (s : seq T) : seq T := take i s ++ drop i.+1 s.

Lemma dels0 (x : T) s : dels 0 (x :: s) = s.
Proof. by rewrite /dels take0 /= drop0. Qed.

Lemma delsS i (x : T) s : dels i.+1 (x :: s) = x :: dels i s.
Proof. by []. Qed.

Lemma dels_nil i : dels i ([::] : seq T) = [::].
Proof. by rewrite /dels; case: i => [|i] //=; rewrite !take_nil.  Qed.

Lemma size_dels i (s : seq T) : (i < size s)%N -> size (dels i s) = (size s).-1.
Proof.
move=> h; rewrite /dels size_cat size_take h size_drop addnBA //.
by rewrite addnC subnS addnK.
Qed.

Lemma size_dels_leq i (s : seq T) : (size (dels i s) <= size s)%N.
Proof.
elim: s i => [|x s IH] i; first by rewrite dels_nil.
case: i => [|i]; first by rewrite dels0 /= leqW.
by rewrite delsS /= ltnS IH.
Qed.

End Dels.

Section Bar.
Variables (p M : nat).
Hypothesis p_gt0 : (0 < p)%N.
Hypothesis M_gt0 : (0 < M)%N.

Definition cellB := (M.-tuple (option 'I_p))%type.

Definition sqB (c : cellB) : seq 'I_p := pmap id (val c).

Definition padd (s : seq 'I_p) : cellB :=
  insubd ([tuple of nseq M None] : M.-tuple (option 'I_p))
         (take M ([seq Some x | x <- s] ++ nseq M None)).

Lemma pmap_id_map (s : seq 'I_p) : pmap id [seq Some x | x <- s] = s.
Proof. by elim: s => //= x s ->. Qed.

Lemma pmap_id_nseq k : pmap id (nseq k (None : option 'I_p)) = [::].
Proof. by elim: k. Qed.

Lemma val_padd s : (size s <= M)%N ->
  val (padd s) = [seq Some x | x <- s] ++ nseq (M - size s) None.
Proof.
move=> h; rewrite /padd val_insubd.
have hsz : size (take M ([seq Some x | x <- s] ++ nseq M None)) = M.
  rewrite size_take size_cat size_map size_nseq.
  by case: ifP => // /negbT; rewrite -leqNgt => h2;
     apply/eqP; rewrite eqn_leq h2 leq_addl.
rewrite hsz eqxx take_cat size_map ltnNge h /= take_nseq //.
by rewrite leq_subr.
Qed.

Lemma sq_padd s : (size s <= M)%N -> sqB (padd s) = s.
Proof.
move=> h; rewrite /sqB val_padd // pmap_cat pmap_id_map pmap_id_nseq cats0.
by [].
Qed.

Lemma size_sqB c : (size (sqB c) <= M)%N.
Proof.
rewrite /sqB size_pmap -[X in (_ <= X)%N](size_tuple c).
exact: count_size.
Qed.

Definition v0 : 'I_p := Ordinal p_gt0.

Lemma dels_map (T U : Type) (f : T -> U) i (s : seq T) :
  [seq f x | x <- dels i s] = dels i [seq f x | x <- s].
Proof. by rewrite /dels map_cat map_take map_drop. Qed.

(** ** the chain complex *)

Section Ring.
Variable R : comNzRingType.
Local Abbreviation chainB := {ffun cellB -> R^o}.

Definition bterm (s : seq 'I_p) (i : nat) : chainB :=
  (-1) ^+ i *: cc (padd (dels i s)).

Definition bdB1 (c : cellB) : chainB :=
  if (1 < size (sqB c))%N
  then \sum_(i < M | (i < size (sqB c))%N) bterm (sqB c) i else 0.

Definition bdB : chainB -> chainB := lin bdB1.

Lemma bdBD x y : bdB (x + y) = bdB x + bdB y. Proof. exact: linD. Qed.
Lemma bdBZ a x : bdB (a *: x) = a *: bdB x. Proof. exact: linZ. Qed.
Lemma bdB_cc c : bdB (cc c) = bdB1 c. Proof. exact: lin_cc. Qed.

Lemma bdB1_padd s : (size s <= M)%N ->
  bdB1 (padd s) =
  if (1 < size s)%N then \sum_(i < M | (i < size s)%N) bterm s i else 0.
Proof. by move=> h; rewrite /bdB1 sq_padd. Qed.

(** ** the cyclic ℤ_p action *)

Definition nuB1 (c : cellB) : chainB := cc (padd [seq shp p_gt0 x | x <- sqB c]).
Definition nuB : chainB -> chainB := lin nuB1.

Lemma nuBD x y : nuB (x + y) = nuB x + nuB y. Proof. exact: linD. Qed.
Lemma nuBZ a x : nuB (a *: x) = a *: nuB x. Proof. exact: linZ. Qed.
Lemma nuB_cc c : nuB (cc c) = nuB1 c. Proof. exact: lin_cc. Qed.
Lemma nuB0 : nuB 0 = 0. Proof. exact: lin0. Qed.

Lemma bdB_nuB1 c : bdB (nuB1 c) = nuB (bdB1 c).
Proof.
set s := sqB c; have hs : (size s <= M)%N := size_sqB c.
have hms : (size [seq shp p_gt0 x | x <- s] <= M)%N by rewrite size_map.
rewrite /nuB1 -/s bdB_cc (bdB1_padd hms) size_map /bdB1 -/s.
case: ifP => hn; last by rewrite nuB0.
rewrite /nuB lin_sum_cond; apply: eq_bigr => i hi.
rewrite /bterm linZ lin_cc /nuB1 sq_padd; last first.
  by rewrite (leq_trans (size_dels_leq _ _)).
by rewrite dels_map.
Qed.

Lemma bdB_nuB x : bdB (nuB x) = nuB (bdB x).
Proof.
apply: (chain_ext (F := fun y => bdB (nuB y)) (G := fun y => nuB (bdB y))).
- by move=> c1 c2; rewrite nuBD bdBD.
- by move=> a c; rewrite nuBZ bdBZ.
- by move=> c1 c2; rewrite bdBD nuBD.
- by move=> a c; rewrite bdBZ nuBZ.
- by move=> c; rewrite nuB_cc bdB_cc bdB_nuB1.
Qed.

(** ** the contraction: prepend the neutral element *)

Definition DB1 (c : cellB) : chainB := cc (padd (v0 :: sqB c)).
Definition DB : chainB -> chainB := lin DB1.

Lemma DB0 : DB 0 = 0. Proof. exact: lin0. Qed.

Definition cterm (s : seq 'I_p) (i : nat) : chainB :=
  (-1) ^+ i *: cc (padd (v0 :: dels i s)).

Lemma bdB_DB1 s : (0 < size s)%N -> (size s < M)%N ->
  bdB (DB1 (padd s)) = cc (padd s) - \sum_(i < M | (i < size s)%N) cterm s i.
Proof.
move=> h0 hM; have hs : (size s <= M)%N by exact: ltnW.
have hvs : (size (v0 :: s) <= M)%N by rewrite /= hM.
rewrite /DB1 sq_padd // bdB_cc (bdB1_padd hvs) /=.
rewrite ltnS h0 -(big_ord_widen _ (fun i => bterm (v0 :: s) i) hM).
rewrite big_ord_recl /bterm dels0 expr0 scale1r; congr (_ + _).
rewrite -(big_ord_widen _ (fun i => cterm s i) hs) -sumrN.
apply: eq_bigr => i _; rewrite /bterm /cterm /bump /=.
by rewrite delsS exprS mulN1r scaleNr.
Qed.

Lemma DB_bd1 s : (size s <= M)%N ->
  DB (bdB1 (padd s))
  = if (1 < size s)%N then \sum_(i < M | (i < size s)%N) cterm s i else 0.
Proof.
move=> hs; rewrite bdB1_padd //; case: ifP => hn; last by rewrite DB0.
rewrite /DB lin_sum_cond; apply: eq_bigr => i hi.
rewrite /bterm linZ lin_cc /DB1 sq_padd //.
by rewrite (leq_trans (size_dels_leq _ _)).
Qed.

Lemma bdB_DB_padd s : (0 < size s)%N -> (size s < M)%N ->
  bdB (DB1 (padd s)) + DB (bdB1 (padd s))
  = cc (padd s) - (if size s == 1%N then cc (padd [:: v0]) else 0).
Proof.
move=> h0 hM; rewrite (bdB_DB1 h0 hM) (DB_bd1 (ltnW hM)).
case hn : (1 < size s)%N.
  have -> : (size s == 1%N) = false by rewrite eqn_leq leqNgt hn.
  by rewrite subr0 addrNK.
have hs1 : size s = 1%N.
  by apply/eqP; rewrite eqn_leq h0 andbT leqNgt hn.
rewrite hs1 eqxx addr0; congr (_ - _).
rewrite -(big_ord_widen _ (fun i => cterm s i) M_gt0) big_ord_recl big_ord0 addr0.
rewrite /cterm expr0 scale1r.
have hd : dels 0 s = [::] by move: hs1 h0 hM hn; case: s => [//|x [|y s']].
by rewrite hd.
Qed.

(** ** the action has order [p] *)

Lemma val_shp_iter r (x : 'I_p) : val (iter r (shp p_gt0) x) = ((val x + r) %% p)%N.
Proof.
elim: r => [|r IH] /=; first by rewrite addn0 modn_small.
rewrite /shp /= IH.
by rewrite -addn1 modnDml addn1 addnS.
Qed.

Lemma shp_iter_p (x : 'I_p) : iter p (shp p_gt0) x = x.
Proof. by apply/val_inj; rewrite val_shp_iter modnDr modn_small // ltn_ord. Qed.

Lemma nuB_iter_padd r s : (size s <= M)%N ->
  iter r nuB (cc (padd s)) = cc (padd [seq iter r (shp p_gt0) x | x <- s]).
Proof.
move=> h; elim: r => [|r IH]; first by rewrite /= map_id.
rewrite iterS IH nuB_cc /nuB1 sq_padd ?size_map // -map_comp.
by congr (cc (padd _)); apply: eq_map => x /=.
Qed.

Lemma iter_nuB_lin r (x : chainB) :
  iter r nuB x = lin (fun c => iter r nuB (cc c)) x.
Proof.
apply: (chain_ext (F := fun y => iter r nuB y)
                  (G := fun y => lin (fun c => iter r nuB (cc c)) y)) => //.
- by elim: r => [|r IH] c1 c2 //=; rewrite IH nuBD.
- by elim: r => [|r IH] a c //=; rewrite IH nuBZ.
- by move=> c1 c2; exact: linD.
- by move=> a c; exact: linZ.
- by move=> c; rewrite lin_cc.
Qed.

Lemma nuB_iter_p (x : chainB) :
  (forall c, x c != 0 -> padd (sqB c) = c) -> iter p nuB x = x.
Proof.
move=> hx; rewrite iter_nuB_lin -[RHS]lin_cc_id.
apply: lin_eq_supp => c hc; rewrite -(hx c hc) nuB_iter_padd ?size_sqB //.
by rewrite (eq_map shp_iter_p) map_id.
Qed.

(** ** the contraction kills homogeneous cycles *)

Definition augB (x : chainB) : R := \sum_(c : cellB) x c.

Lemma bdB_DB_hom (x : chainB) (k : nat) :
  (forall c, x c != 0 -> padd (sqB c) = c /\ size (sqB c) = k) ->
  (0 < k)%N -> (k < M)%N -> bdB x = 0 -> (k = 1%N -> augB x = 0) ->
  bdB (DB x) = x.
Proof.
move=> hx h0 hM hbd haug.
rewrite {1}/DB /bdB lin_comp.
have hstep : lin (fun c => lin bdB1 (DB1 c)) x
           = lin (fun c => cc c - (if k == 1%N then cc (padd [:: v0]) else 0)
                           - lin DB1 (bdB1 c)) x.
  apply: lin_eq_supp => c hc; have [hn hk] := hx c hc.
  have h1 : (0 < size (sqB c))%N by rewrite hk.
  have h2 : (size (sqB c) < M)%N by rewrite hk.
  move: (bdB_DB_padd h1 h2); rewrite hn hk => e.
  by rewrite -/(bdB _) -/(DB _) -e addrK.
rewrite hstep.
rewrite (_ : lin _ x = lin cc x
             - lin (fun _ : cellB => if k == 1%N then cc (padd [:: v0]) else 0) x
             - lin (fun c => lin DB1 (bdB1 c)) x); last first.
  rewrite /lin -!sumrB; apply: eq_bigr => c _.
  by rewrite !scalerBr.
rewrite lin_cc_id -lin_comp.
have -> : lin bdB1 x = 0 by exact: hbd.
rewrite lin0 subr0.
case hk1 : (k == 1%N); last first.
  by rewrite /lin big1 ?subr0 // => c _; rewrite scaler0.
rewrite (_ : lin _ x = augB x *: cc (padd [:: v0])); last first.
  by rewrite /lin /augB scaler_suml.
by rewrite haug ?scale0r ?subr0 //; apply/eqP.
Qed.

(** ** the HSSZ co-hemisphere cochains, on the bar complex

    [salt.v] states them on value sequences with [delete i] as face maps, which
    is exactly the bar complex; here they become genuine cochains and the two
    Stokes relations become chain-level identities. *)

Definition natseq (c : cellB) : seq nat := [seq val x | x <- sqB c].

Definition phi (d : nat) (x : chainB) : R :=
  \sum_(c : cellB) x c * (Phi p d (natseq c))%:R.

Lemma size_natseq c : size (natseq c) = size (sqB c).
Proof. exact: size_map. Qed.

Lemma all_natseq c : all (fun y => (y < p)%N) (natseq c).
Proof. by apply/allP => y /mapP[x _ ->]; rewrite ltn_ord. Qed.

Lemma natseq_padd s : (size s <= M)%N -> natseq (padd s) = [seq val x | x <- s].
Proof. by move=> h; rewrite /natseq sq_padd. Qed.

Lemma phiD d x y : phi d (x + y) = phi d x + phi d y.
Proof.
by rewrite /phi -big_split; apply: eq_bigr => c _; rewrite ffunE mulrDl.
Qed.

Lemma phiZ d a x : phi d (a *: x) = a * phi d x.
Proof.
rewrite /phi mulr_sumr; apply: eq_bigr => c _.
by rewrite scale_ffunE mulrA.
Qed.

Lemma phi0 d : phi d 0 = 0.
Proof. by rewrite -(scale0r 0) phiZ mul0r. Qed.

Lemma phi_cc d c : phi d (cc c) = (Phi p d (natseq c))%:R.
Proof.
rewrite /phi (bigD1 c) //= ccE eqxx mul1r big1 ?addr0 // => c' hc'.
by rewrite ccE (negbTE hc') mul0r.
Qed.

Lemma phi_sum d (I : finType) (P : pred I) (F : I -> chainB) :
  phi d (\sum_(i | P i) F i) = \sum_(i | P i) phi d (F i).
Proof.
rewrite /phi exchange_big /=; apply: eq_bigr => c _.
by rewrite sum_ffunE mulr_suml.
Qed.

Lemma phi_lin d (f : cellB -> chainB) (x : chainB) :
  phi d (lin f x) = \sum_(c : cellB) x c * phi d (f c).
Proof.
rewrite /lin phi_sum; apply: eq_bigr => c _.
by rewrite phiZ.
Qed.

Lemma delsE i (u : seq nat) : dels i u = delete i u.
Proof. by []. Qed.

Lemma val_shp_sh (x : 'I_p) : val (shp p_gt0 x) = sh p (val x).
Proof.
rewrite /shp /sh /=; case: ifP => h; first by rewrite modn_small.
have e : ((val x).+1 = p)%N by apply/eqP; rewrite eqn_leq ltn_ord /= leqNgt h.
by rewrite e modnn.
Qed.

Lemma natseq_nuB1 c : natseq (padd [seq shp p_gt0 x | x <- sqB c])
                    = [seq sh p y | y <- natseq c].
Proof.
rewrite natseq_padd ?size_map ?size_sqB // /natseq -!map_comp.
by apply: eq_map => x /=; exact: val_shp_sh.
Qed.

Lemma phi_nuB1 d c : phi d (nuB1 c) = (Phi p d [seq sh p y | y <- natseq c])%:R.
Proof. by rewrite /nuB1 phi_cc natseq_nuB1. Qed.

Lemma phi_iter_nuB d r c :
  phi d (iter r nuB (cc c)) = (Phi p d (shiftv p r (natseq c)))%:R.
Proof.
elim: r c => [|r IH] c; first by rewrite /= phi_cc.
rewrite iterSr nuB_cc /nuB1 IH natseq_nuB1.
by rewrite /shiftv iterSr.
Qed.

Lemma phi_bdB1 d c :
  phi d (bdB1 c) =
  if (1 < size (sqB c))%N
  then \sum_(i < M | (i < size (sqB c))%N)
         (-1) ^+ (val i) * (Phi p d (delete i (natseq c)))%:R
  else 0.
Proof.
rewrite /bdB1; case: ifP => hn; last exact: phi0.
rewrite phi_sum; apply: eq_bigr => i hi.
rewrite /bterm phiZ phi_cc natseq_padd; last first.
  by rewrite (leq_trans (size_dels_leq _ _)) // size_sqB.
by rewrite /natseq dels_map.
Qed.

(** the two Stokes relations, on a basis cell *)

Lemma phi_bd_even_cc l c : ((2 * l).+2 <= M)%N ->
  phi (2 * l) (bdB1 c) = phi (2 * l).+1 (nuB1 c) - phi (2 * l).+1 (cc c).
Proof.
move=> hM; set n := size (sqB c).
have hns : size (natseq c) = n by rewrite size_natseq.
case hn2 : (n == (2 * l).+2).
  have hn : (1 < n)%N by rewrite (eqP hn2).
  rewrite phi_bdB1 -/n hn phi_nuB1 phi_cc.
  rewrite -(big_ord_widen _
     (fun i => (-1) ^+ i * (Phi p (2 * l) (delete i (natseq c)))%:R));
    last by rewrite -/n (eqP hn2).
  have hnn : n = (2 * l).+2 by apply/eqP.
  rewrite hnn.
  have hns2 : size (natseq c) = (2 * l).+2 by rewrite hns hnn.
  by rewrite (Phi_bd_even p_gt0 R hns2 (all_natseq c)).
have hne : size (natseq c) != (2 * l).+2 by rewrite hns hn2.
have hne2 : size [seq sh p y | y <- natseq c] != (2 * l).+2 by rewrite size_map.
rewrite phi_nuB1 phi_cc (Phi_size p hne) (Phi_size p hne2) subrr.
rewrite phi_bdB1 -/n; case: ifP => hn; last by [].
rewrite big1 // => i hi.
have hd : size (delete i (natseq c)) != (2 * l).+1.
  rewrite -delsE size_dels ?hns //; apply/eqP => e.
  by move: hn2; rewrite -(prednK (_ : (0 < n)%N)) ?e ?eqxx // (leq_trans _ hn).
by rewrite (Phi_size p hd) mulr0.
Qed.

Lemma phi_bd_odd_cc l c : ((2 * l).+3 <= M)%N ->
  phi (2 * l).+1 (bdB1 c) = \sum_(r < p) phi (2 * l).+2 (iter r nuB (cc c)).
Proof.
move=> hM; set n := size (sqB c).
have hns : size (natseq c) = n by rewrite size_natseq.
rewrite (eq_bigr (fun r : 'I_p => (Phi p (2 * l).+2 (shiftv p r (natseq c)))%:R));
  last by move=> r _; rewrite phi_iter_nuB.
case hn3 : (n == (2 * l).+3).
  have hn : (1 < n)%N by rewrite (eqP hn3).
  rewrite phi_bdB1 -/n hn.
  rewrite -(big_ord_widen _
     (fun i => (-1) ^+ i * (Phi p (2 * l).+1 (delete i (natseq c)))%:R));
    last by rewrite -/n (eqP hn3).
  have hnn : n = (2 * l).+3 by apply/eqP.
  rewrite hnn.
  have hns3 : size (natseq c) = (2 * l).+3 by rewrite hns hnn.
  by rewrite (Phi_bd_odd p_gt0 R hns3 (all_natseq c)).
rewrite big1; last first.
  move=> r _.
  have hsz : size (shiftv p r (natseq c)) != (2 * l).+3 by rewrite size_shiftv hns hn3.
  by rewrite (Phi_size p hsz).
rewrite phi_bdB1 -/n; case: ifP => hn; last by [].
rewrite big1 // => i hi.
have hd : size (delete i (natseq c)) != (2 * l).+2.
  rewrite -delsE size_dels ?hns //; apply/eqP => e.
  by move: hn3; rewrite -(prednK (_ : (0 < n)%N)) ?e ?eqxx // (leq_trans _ hn).
by rewrite (Phi_size p hd) mulr0.
Qed.

(** the two Stokes relations, on chains *)

Lemma phi_bd_even l x : ((2 * l).+2 <= M)%N ->
  phi (2 * l) (bdB x) = phi (2 * l).+1 (nuB x) - phi (2 * l).+1 x.
Proof.
move=> hM; rewrite -{3}[x]lin_cc_id /bdB /nuB !phi_lin -sumrB.
apply: eq_bigr => c _.
by rewrite -mulrBr (phi_bd_even_cc c hM).
Qed.

Lemma phi_bd_odd l x : ((2 * l).+3 <= M)%N ->
  phi (2 * l).+1 (bdB x) = \sum_(r < p) phi (2 * l).+2 (iter r nuB x).
Proof.
move=> hM; rewrite /bdB phi_lin.
rewrite [RHS](eq_bigr (fun r : 'I_p =>
   \sum_(c : cellB) x c * phi (2 * l).+2 (iter r nuB (cc c)))); last first.
  by move=> r _; rewrite (iter_nuB_lin r x) phi_lin.
rewrite exchange_big /=; apply: eq_bigr => c _.
by rewrite (phi_bd_odd_cc c hM) mulr_sumr.
Qed.

(** the base case *)

Lemma phi0_orbit c : (size (sqB c) = 1)%N ->
  \sum_(r < p) phi 0 (iter r nuB (cc c)) = 1.
Proof.
move=> h1; have : size (natseq c) = 1%N by rewrite size_natseq.
case hc : (natseq c) => [|v [|w u]] // _.
rewrite (eq_bigr (fun r : 'I_p => (Phi p 0 (shiftv p r (natseq c)))%:R));
  last by move=> r _; rewrite phi_iter_nuB.
rewrite hc; apply: (Phi0_shift p_gt0 R).
by have := all_natseq c; rewrite hc /= andbT.
Qed.

End Ring.
End Bar.
