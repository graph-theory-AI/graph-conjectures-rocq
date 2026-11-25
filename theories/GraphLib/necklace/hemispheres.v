(** * The hemisphere chains of the Z_p-Tucker lemma

    Meunier (2014), Section 3.3, formulas (5) to (7).  This file defines the action [nu] of Z_p on
    the chains of R^N, its sum over the group, and the hemisphere chains h_d, with
    - h_0 is the vertex (o, ..., o, (n, 1));
    - the boundary of h_(2l) is (nu - id) h_(2l-1), and that of h_(2l+1) is the sum over the group
      of the images of h_(2l);
    - each cell of h_d has a coordinate that is the end of a path, so that h_d is a chain of K. *)

From mathcomp Require Import boot algebra.
From GC.GraphLib.necklace Require Import chains cubical necklace_complex.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Set SsrOldRewriteGoalsOrder.
Local Open Scope ring_scope.

Section Hemi.
Variables (n p N : nat) (R : comNzRingType).
Hypothesis n_gt0 : (0 < n)%N.
Hypothesis p_gt0 : (0 < p)%N.
Hypothesis pR : (p%:R = 0 :> R).
Hypothesis N_gt0 : (0 < N)%N.

Local Abbreviation cut := (cut n p).
Local Abbreviation cell1 := (cell1 n p).
Local Abbreviation cellN := (cellN n p N).
Local Abbreviation chain := {ffun cellN -> R^o}.

Definition p1 : 'I_p := Ordinal p_gt0.
Definition topk : 'I_n := rev_ord (Ordinal n_gt0).
Definition topv : cut := Some (topk, p1).
Definition o_cell : cellN := [ffun _ => Vtx None].
Definition setc (c : cellN) (j : 'I_N) (x : cell1) : cellN :=
  [ffun i => if i == j then x else c i].

(** ** Part 1 — the ν action *)

Definition shiftp (r : 'I_p) : 'I_p := Ordinal (ltn_pmod r.+1 p_gt0).
Definition shift1v (v : cut) : cut := omap (fun kr => (kr.1, shiftp kr.2)) v.
Definition shift1 (x : cell1) : cell1 :=
  match x with inl v => inl (shift1v v) | inr kr => inr (kr.1, shiftp kr.2) end.
Definition shift (c : cellN) : cellN := [ffun i => shift1 (c i)].
Definition nu : chain -> chain := lin (fun c : cellN => cc (shift c) : chain).

Lemma nu_cc c : nu (cc c) = cc (shift c). Proof. exact: lin_cc. Qed.
Lemma nuD x y : nu (x + y) = nu x + nu y. Proof. exact: linD. Qed.

Lemma nuB x y : nu (x - y) = nu x - nu y. Proof. exact: linB. Qed.
Lemma nu0 : nu 0 = 0. Proof. exact: lin0. Qed.

Lemma nu_sum (I : Type) (rr : seq I) (F : I -> chain) :
  nu (\sum_(i <- rr) F i) = \sum_(i <- rr) nu (F i).
Proof. by elim/big_rec2: _ => [|i a b _ <-]; rewrite ?nu0 ?nuD. Qed.

Lemma bd_sum (I : Type) (rr : seq I) (F : I -> chain) :
  bd (\sum_(i <- rr) F i) = \sum_(i <- rr) bd (F i).
Proof. by elim/big_rec2: _ => [|i a b _ <-]; rewrite ?(@bdD n p N R) //; rewrite /bd lin0. Qed.

Lemma lin_id (x : chain) : lin (fun c => cc c) x = x.
Proof. by rewrite /lin {2}[x]chain_decomp. Qed.

Definition nupow (r : nat) : chain -> chain := iter r nu.
Definition sigma (x : chain) : chain := \sum_(r < p) nupow r x.

Lemma shift1_is_edge x : is_edge (shift1 x) = is_edge x.
Proof. by case: x. Qed.

Lemma shift_is_edge c i : is_edge (shift c i) = is_edge (c i).
Proof. by rewrite ffunE shift1_is_edge. Qed.

Lemma shift_fv c j v : shift (fv c j v) = fv (shift c) j (shift1v v).
Proof.
apply/ffunP => i; rewrite /shift !ffunE.
by case: (i == j).
Qed.

Lemma shift_etop kr : shift1v (etop kr) = etop (kr.1, shiftp kr.2).
Proof. by case: kr. Qed.

Lemma shift_ebot kr : shift1v (ebot kr) = ebot (kr.1, shiftp kr.2).
Proof. by case: kr => k r; rewrite /ebot /= /slide; case: (k == 0 :> nat). Qed.

Lemma rk_shift c j : rk (shift c) j = rk c j.
Proof.
by rewrite /rk; apply: eq_card => i; rewrite !inE shift_is_edge.
Qed.

(** bd commutes with ν, hence is a chain map. *)
Lemma bd1_shift c : bd1 (shift c) = nu (bd1 c).
Proof.
rewrite /bd1 /nu lin_sum; apply: eq_bigr => j _.
rewrite /edgeterm ffunE.
case E : (c j) => [v|kr] /=; first by rewrite lin0.
rewrite rk_shift linZ linB !lin_cc.
by rewrite !shift_fv shift_etop shift_ebot.
Qed.

Lemma bd_nu x : bd (nu x) = nu (bd x).
Proof.
rewrite /bd /nu !lin_comp /lin; apply: eq_bigr => c _; congr (_ *: _).
by rewrite -/(lin bd1 (cc (shift c))) lin_cc bd1_shift.
Qed.

Lemma nupow_lin r x : nupow r x = lin (fun c => cc (iter r shift c)) x.
Proof.
elim: r => [|r IH]; first by rewrite /nupow /= lin_id.
rewrite /nupow iterS -/(nupow r x) IH /nu lin_comp.
apply: eq_bigr => c _; congr (_ *: _).
by rewrite -/(lin (fun c0 => cc (shift c0)) (cc (iter r shift c))) lin_cc iterS.
Qed.

Lemma bd_nupow r x : bd (nupow r x) = nupow r (bd x).
Proof.
elim: r => [//|r IH].
by rewrite /nupow !iterS -/(nupow r x) -/(nupow r (bd x)) bd_nu IH.
Qed.

Lemma bd_sigma x : bd (sigma x) = sigma (bd x).
Proof. by rewrite /sigma bd_sum; apply: eq_bigr => r _; rewrite bd_nupow. Qed.

Lemma shiftp_pow_val r v : val (iter r shiftp v) = ((val v + r) %% p)%N.
Proof.
elim: r => [|r IH] /=; first by rewrite addn0 modn_small.
rewrite -addn1 -modnDml IH modnDml.
by rewrite modnDml addn1 addnS.
Qed.

Lemma shiftp_pow_p : iter p shiftp =1 id.
Proof.
move=> v; apply/val_inj; rewrite shiftp_pow_val -modnDmr modnn addn0 modn_small //.
exact: ltn_ord.
Qed.

Lemma iter_shift1v r v : iter r shift1v v = omap (fun kr => (kr.1, iter r shiftp kr.2)) v.
Proof. by elim: r v => [|r IH] [[k s]|] //=; rewrite IH. Qed.

Lemma iter_shift1_inl r v : iter r shift1 (inl v) = inl (iter r shift1v v).
Proof. by elim: r => //= r ->. Qed.

Lemma iter_shift1_inr r kr : iter r shift1 (inr kr) = inr (kr.1, iter r shiftp kr.2).
Proof. by elim: r kr => [|r IH] [k s] //=; rewrite IH. Qed.

Lemma shift1_pow_p : iter p shift1 =1 id.
Proof.
case=> [v|kr].
- rewrite iter_shift1_inl iter_shift1v; case: v => [[k r]|] //=.
  by rewrite shiftp_pow_p.
- by rewrite iter_shift1_inr; case: kr => k r /=; rewrite shiftp_pow_p.
Qed.

Lemma nupowD r x y : nupow r (x + y) = nupow r x + nupow r y.
Proof. by elim: r => [//|r IH]; rewrite /nupow !iterS -/(nupow r _) IH nuD. Qed.

Lemma nupowB r x y : nupow r (x - y) = nupow r x - nupow r y.
Proof. by elim: r => [//|r IH]; rewrite /nupow !iterS -/(nupow r _) IH nuB. Qed.

Lemma iter_shift r c : iter r shift c = [ffun i => iter r shift1 (c i)].
Proof.
elim: r => [|r IH]; first by apply/ffunP => i; rewrite ffunE.
by rewrite iterS IH /shift; apply/ffunP => i; rewrite !ffunE iterS.
Qed.

Lemma nupow_p x : nupow p x = x.
Proof.
rewrite nupow_lin -[RHS]lin_id; apply: eq_bigr => c _; congr (_ *: cc _).
by rewrite iter_shift; apply/ffunP => i; rewrite ffunE shift1_pow_p.
Qed.

Lemma nupow_modS (r : 'I_p) x : nupow r.+1 x = nupow (val (shiftp r)) x.
Proof.
rewrite /shiftp /=; case: (ltngtP r.+1 p) => [h|h|h].
- by rewrite modn_small.
- by rewrite ltnS leqNgt ltn_ord in h.
- rewrite -[nu (nupow r x)]/(nupow r.+1 x) h nupow_p modnn.
  by rewrite /nupow /=.
Qed.

Lemma shiftp_inj : injective shiftp.
Proof.
have inv : cancel shiftp (iter p.-1 shiftp).
  by move=> a; rewrite -iterSr prednK // shiftp_pow_p.
exact: can_inj inv.
Qed.

Lemma nusigma x : nu (sigma x) = sigma x.
Proof.
rewrite /sigma nu_sum.
rewrite (eq_bigr (fun r => nupow (val (shiftp r)) x)); last first.
  by move=> r _; rewrite -nupow_modS.
by rewrite [RHS](reindex_inj shiftp_inj).
Qed.

Lemma nupow_nu r x : nupow r (nu x) = nupow r.+1 x.
Proof. by rewrite /nupow -iterSr. Qed.

Lemma sigma_nu x : sigma (nu x) = sigma x.
Proof.
rewrite /sigma.
rewrite (eq_bigr (fun r => nupow (val (shiftp r)) x)); last first.
  by move=> r _; rewrite nupow_nu -nupow_modS.
by rewrite [RHS](reindex_inj shiftp_inj).
Qed.

Lemma sigmaD x y : sigma (x + y) = sigma x + sigma y.
Proof. by rewrite /sigma -big_split; apply: eq_bigr => r _; rewrite nupowD. Qed.

Lemma sigmaB x y : sigma (x - y) = sigma x - sigma y.
Proof. by rewrite /sigma -sumrB; apply: eq_bigr => r _; rewrite nupowB. Qed.

Lemma sigma_nuid x : sigma (nu x - x) = 0.
Proof. by rewrite sigmaB sigma_nu subrr. Qed.

Lemma shift_ocell : shift o_cell = o_cell.
Proof. by apply/ffunP => i; rewrite /shift /o_cell !ffunE. Qed.

Lemma nupow_ocell r : nupow r (cc o_cell) = cc o_cell.
Proof.
by elim: r => [//|r IH]; rewrite /nupow iterS -/(nupow r _) IH nu_cc shift_ocell.
Qed.

Lemma sigma_ocell : sigma (cc o_cell) = 0.
Proof.
rewrite /sigma (eq_bigr (fun=> cc o_cell)); last by move=> r _; rewrite nupow_ocell.
by rewrite sumr_const card_ord -scaler_nat pR scale0r.
Qed.

(** ** Part 2 — the path chain P_1 and its boundary *)

Definition consP (j : 'I_N) (X : chain) : chain :=
  lin (fun c => \sum_(k : 'I_n) cc (setc c j (Edg (k, p1)))) X.
Definition topcoord (j : 'I_N) (X : chain) : chain :=
  lin (fun c => cc (setc c j (Vtx topv))) X.

Lemma consPD j x y : consP j (x + y) = consP j x + consP j y. Proof. exact: linD. Qed.
Lemma consPZ j a x : consP j (a *: x) = a *: consP j x. Proof. exact: linZ. Qed.
Lemma consPB j x y : consP j (x - y) = consP j x - consP j y. Proof. exact: linB. Qed.
Lemma consP0 j : consP j 0 = 0. Proof. exact: lin0. Qed.
Lemma consP_cc j c : consP j (cc c) = \sum_(k : 'I_n) cc (setc c j (Edg (k, p1))).
Proof. exact: lin_cc. Qed.

Lemma topcoordD j x y : topcoord j (x + y) = topcoord j x + topcoord j y. Proof. exact: linD. Qed.
Lemma topcoordZ j a x : topcoord j (a *: x) = a *: topcoord j x. Proof. exact: linZ. Qed.
Lemma topcoord_cc j c : topcoord j (cc c) = cc (setc c j (Vtx topv)). Proof. exact: lin_cc. Qed.

Lemma setc_id (c : cellN) j : c j = Vtx None -> setc c j (Vtx None) = c.
Proof. by move=> h; apply/ffunP => i; rewrite ffunE; case: eqP => // ->. Qed.

(** boundary of the single P_1 prepended on the trivial chain: telescopes. *)
Lemma bd_P1 j : bd (consP j (cc o_cell)) = cc (setc o_cell j (Vtx topv)) - cc o_cell.
Proof.
pose vm (m : nat) : cut := if m == 0 then None else Some (insubd (Ordinal n_gt0) m.-1, p1).
pose phi (m : nat) : chain := cc (setc o_cell j (Vtx (vm m))).
rewrite consP_cc bd_sum.
transitivity (\sum_(k : 'I_n) (phi (val k).+1 - phi (val k))); last first.
  rewrite -(big_mkord xpredT (fun m => phi m.+1 - phi m)) telescope_sumr //.
  congr (_ - _); rewrite /phi /vm /=.
  - rewrite ifF; last by apply/negbTE; rewrite -lt0n.
    congr (cc (setc o_cell j (Vtx (Some (_, p1))))); apply/val_inj => /=.
    rewrite val_insubd /topk /= subn1.
    by rewrite ltn_predL n_gt0.
  - by rewrite setc_id // /o_cell ffunE.
apply: eq_bigr => k _.
rewrite bd_cc /bd1 (bigD1 j) //= big1; last first.
  by move=> i inej; rewrite /edgeterm ffunE (negbTE inej) /o_cell ffunE.
rewrite addr0 /edgeterm ffunE eqxx.
have rk0 : rk (setc o_cell j (Edg (k, p1))) j = 0.
  apply/eqP; rewrite cards_eq0; apply/eqP/setP => i; rewrite !inE ffunE.
  case: (eqVneq i j) => [->|inej]; first by rewrite ltnn andbF.
  by rewrite /o_cell ffunE.
have fvset (v : cut) : fv (setc o_cell j (Edg (k, p1))) j v = setc o_cell j (Vtx v).
  by apply/ffunP => i; rewrite !ffunE; case: (i == j).
rewrite /Edg /= rk0 expr0 scale1r fvset fvset.
congr (_ - _); rewrite /phi /vm /=.
  congr (cc (setc o_cell j (Vtx _))).
  rewrite /etop; congr (Some (_, p1)); apply/val_inj; rewrite val_insubd /=.
  by rewrite ltn_ord.
rewrite /ebot /slide /=; case: (val k == 0) => //.
congr (cc (setc o_cell j (Vtx (Some (_, p1))))); apply/val_inj => /=.
by rewrite val_insubd /= (leq_ltn_trans (leq_pred _) (ltn_ord k)).
Qed.

(** ** Part 3 — the hemisphere chains and the boundary relations *)

Lemma pc_proof (d : nat) : ((N - d).-1 < N)%N.
Proof.
apply: (@leq_ltn_trans N.-1); last by rewrite ltn_predL.
by rewrite -!subn1 leq_sub2r // leq_subr.
Qed.
Definition pc (d : nat) : 'I_N := Ordinal (pc_proof d).

Fixpoint htil (d : nat) : chain :=
  match d with
  | 0 => cc o_cell
  | d'.+1 => (if odd d' then (fun x => nu x - x) else sigma) (consP (pc d') (htil d'))
  end.

Definition h (d : nat) : chain := bd (consP (pc d) (htil d)) + htil d.

Definition opd (d : nat) (x : chain) : chain :=
  if odd d then nu x - x else sigma x.

Lemma opdD d x y : opd d (x + y) = opd d x + opd d y.
Proof.
rewrite /opd; case: (odd d); last exact: sigmaD.
by rewrite nuD addrACA opprD.
Qed.

Lemma opdB d x y : opd d (x - y) = opd d x - opd d y.
Proof.
rewrite /opd; case: (odd d); last exact: sigmaB.
by rewrite nuB !opprB addrACA [in RHS]addrACA; congr (_ + _); rewrite addrC.
Qed.

Lemma bd_opd d x : bd (opd d x) = opd d (bd x).
Proof.
rewrite /opd; case: (odd d); last exact: bd_sigma.
by rewrite [bd (nu x - x)](linB bd1) -/(bd (nu x)) -/(bd x) bd_nu.
Qed.

Lemma opd_kills_htil d : opd d (htil d) = 0.
Proof.
case: d => [|d] /=; first by rewrite /opd /= sigma_ocell.
rewrite /opd /=; case: (odd d) => /=.
- by rewrite sigma_nuid.
- by rewrite nusigma subrr.
Qed.

Lemma hrel d : bd (h d.+1) = opd d (h d).
Proof.
rewrite {1}/h [bd (_ + _)](@bdD n p N R) bd_bd add0r.
have -> : htil d.+1 = opd d (consP (pc d) (htil d)) by rewrite /opd /=; case: (odd d).
by rewrite bd_opd /h opdD opd_kills_htil addr0.
Qed.

Lemma h0_val : h 0 = cc (setc o_cell (pc 0) (Vtx topv)).
Proof. by rewrite /h /= bd_P1 -addrA (addrC (- _)) subrr addr0. Qed.

(** ** Part 4 — h_d ∈ C(K) *)

(** [inX] is [necklace_complex.in_X] specialised to this (generic) N. *)
Definition inX (v : {ffun 'I_N -> cut}) : bool :=
  [forall b : 'I_n, [exists j : 'I_N, covers (v j) b]].

(** support of a relabelling chain [lin (cc o g)]. *)
Lemma lin_cc_supp (g : cellN -> cellN) (X : chain) (d : cellN) :
  (lin (fun c => cc (g c)) X) d != 0 -> exists2 c, X c != 0 & g c = d.
Proof.
move=> hd.
have [/existsP[c /andP[xc /eqP gcd]]|hno] := boolP [exists c, (X c != 0) && (g c == d)].
  by exists c.
move: hd; suff -> : lin (fun c => cc (g c)) X d = 0 by rewrite eqxx.
move/existsPn in hno; rewrite /lin sum_ffunE big1 // => c _.
rewrite ffunE ccE.
have := hno c; rewrite negb_and => /orP[/negbNE/eqP->|]; first by rewrite scale0r.
by rewrite eq_sym => /negbTE ->; rewrite scaler0.
Qed.

(** Support below coordinate j: every basis cell of X is o at coordinates <= j. *)
Definition below (j : 'I_N) (X : chain) : Prop :=
  forall c, X c != 0 -> forall i, (val i <= val j)%N -> c i = Vtx None.

Lemma below_D j x y : below j x -> below j y -> below j (x + y).
Proof.
move=> hx hy c; rewrite ffunE => hc i hi.
have [xc|xc] := eqVneq (x c) 0.
  by apply: hy => //; move: hc; rewrite xc add0r.
by apply: hx.
Qed.

Lemma below0 j : below j 0.
Proof. by move=> c; rewrite ffunE eqxx. Qed.

Lemma below_Z j a x : below j x -> below j (a *: x).
Proof.
move=> hx c; rewrite ffunE => hc i hi; apply: hx => //.
by apply: contra hc => /eqP ->; rewrite scaler0.
Qed.

Lemma below_N j x : below j x -> below j (- x).
Proof.
move=> hx c; rewrite ffunE => hc i hi; apply: hx => //.
by apply: contra hc => /eqP ->; rewrite oppr0.
Qed.

Lemma below_sum j (I : Type) (r : seq I) (F : I -> chain) :
  (forall k, below j (F k)) -> below j (\sum_(k <- r) F k).
Proof. by move=> hF; elim/big_rec: _ => [|k a _ hb]; [exact: below0|exact: below_D]. Qed.

Lemma below_cc j (c : cellN) : (forall i, (val i <= val j)%N -> c i = Vtx None) -> below j (cc c).
Proof.
move=> hc d; rewrite ccE; case: (eqVneq d c) => [dc _ i hi|]; last by rewrite eqxx.
by rewrite dc; exact: hc.
Qed.

Lemma below_bd1 j (c : cellN) :
  (forall i, (val i <= val j)%N -> c i = Vtx None) -> below j (bd1 c).
Proof.
move=> hc; rewrite /bd1; apply: below_sum => i.
rewrite /edgeterm; case E : (c i) => [v|kr]; first exact: below0.
have iNj l : (val l <= val j)%N -> i != l.
  by move=> hl; apply/eqP => eil; move: E; rewrite eil (hc l hl).
apply: below_Z; apply: below_D; last apply: below_N.
all: apply: below_cc => l hl; rewrite fvE eq_sym (negbTE (iNj l hl)); exact: hc.
Qed.

Lemma below_bd j x : below j x -> below j (bd x).
Proof.
move=> hx; rewrite /bd /lin; apply: below_sum => c.
have [->|xc] := eqVneq (x c) 0; first by rewrite scale0r; exact: below0.
by apply: below_Z; apply: below_bd1 => i hi; apply: hx.
Qed.

Lemma below_nu j x : below j x -> below j (nu x).
Proof.
move=> hx; rewrite /nu /lin; apply: below_sum => c.
have [->|xc] := eqVneq (x c) 0; first by rewrite scale0r; exact: below0.
apply: below_Z; apply: below_cc => i hi; rewrite ffunE.
by rewrite (hx c xc i hi).
Qed.

Lemma below_consP (j0 j : 'I_N) x :
  (val j < val j0)%N -> below j0 x -> below j (consP j0 x).
Proof.
move=> jj0 hx; rewrite /consP /lin; apply: below_sum => c.
have [->|xc] := eqVneq (x c) 0; first by rewrite scale0r; exact: below0.
apply: below_Z; apply: below_sum => k.
apply: below_cc => i hi; rewrite ffunE.
have i0 : i != j0 by rewrite -(inj_eq val_inj) neq_ltn (leq_ltn_trans hi jj0).
by rewrite (negbTE i0) (hx c xc i (leq_trans hi (ltnW jj0))).
Qed.

Lemma below_nupow j r x : below j x -> below j (nupow r x).
Proof. by move=> hx; elim: r => [//|r IH]; rewrite /nupow iterS -/(nupow r x); apply: below_nu. Qed.

Lemma below_sigma j x : below j x -> below j (sigma x).
Proof. by move=> hx; rewrite /sigma; apply: below_sum => r; apply: below_nupow. Qed.

Lemma below_opd j d x : below j x -> below j (opd d x).
Proof.
move=> hx; rewrite /opd; case: (odd d); last exact: below_sigma.
by apply: below_D; [apply: below_nu | apply: below_N].
Qed.

Lemma pc_lt d : (d.+1 < N)%N -> (val (pc d.+1) < val (pc d))%N.
Proof.
move=> dN; rewrite /pc /= -[in X in (_ < X)%N]subnS ltn_predL subn_gt0.
exact: dN.
Qed.

Lemma below_htil d : (d < N)%N -> below (pc d) (htil d).
Proof.
elim: d => [_|d IH dN].
  by apply: below_cc => i _; rewrite /o_cell ffunE.
have -> : htil d.+1 = opd d (consP (pc d) (htil d)) by rewrite /opd /=; case: (odd d).
apply: below_opd; apply: (@below_consP (pc d)); first exact: pc_lt.
by apply: IH; apply: ltnW.
Qed.

(** the front-factor boundary law (Lemma 2.3 for prepending P_1) *)

Lemma fv_setc_comm (c : cellN) i j v e :
  i != j -> fv (setc c j e) i v = setc (fv c i v) j e.
Proof.
move=> ij; apply/ffunP => l; rewrite !ffunE.
case: (eqVneq l i) => [->|_]; last by [].
by rewrite (negbTE ij).
Qed.

Lemma rk_setc_below (c : cellN) j k i :
  (forall l, (val l <= val j)%N -> c l = Vtx None) -> (val j < val i)%N ->
  rk (setc c j (Edg (k, p1))) i = (rk c i).+1.
Proof.
move=> hc ji; rewrite /rk.
have -> : [set i0 | is_edge (setc c j (Edg (k, p1)) i0) && (val i0 < val i)%N]
        = j |: [set i0 | is_edge (c i0) && (val i0 < val i)%N].
  apply/setP => l; rewrite !inE ffunE.
  case: (eqVneq l j) => [->|lj] /=; first by rewrite ji.
  by [].
rewrite cardsU1 inE (hc j (leqnn _)) /=.
by [].
Qed.

Lemma fvj (c : cellN) j v e : fv (setc c j e) j v = setc c j (Vtx v).
Proof. by apply/ffunP => l; rewrite fvE !ffunE; case: (l == j). Qed.

Lemma edge_telescope (c : cellN) j : c j = Vtx None ->
  \sum_(k : 'I_n)
     (cc (setc c j (Vtx (Some (k, p1)))) - cc (setc c j (Vtx (slide (Some (k, p1))))))
  = cc (setc c j (Vtx topv)) - cc c :> chain.
Proof.
move=> cj.
pose vm (m : nat) : cut := if m == 0 then None else Some (insubd (Ordinal n_gt0) m.-1, p1).
pose phi (m : nat) : chain := cc (setc c j (Vtx (vm m))).
transitivity (\sum_(k : 'I_n) (phi (val k).+1 - phi (val k))); last first.
  rewrite -(big_mkord xpredT (fun m => phi m.+1 - phi m)) telescope_sumr //.
  congr (_ - _); rewrite /phi /vm /=.
  - rewrite ifF; last by apply/negbTE; rewrite -lt0n.
    congr (cc (setc c j (Vtx (Some (_, p1))))); apply/val_inj => /=.
    by rewrite val_insubd /topk /= subn1 ltn_predL n_gt0.
  - by rewrite setc_id.
apply: eq_bigr => k _; congr (_ - _); rewrite /phi /vm /=.
  congr (cc (setc c j (Vtx (Some (_, p1))))); apply/val_inj => /=.
  by rewrite val_insubd ltn_ord.
case: (k == 0 :> nat) => //.
congr (cc (setc c j (Vtx (Some (_, p1))))); apply/val_inj => /=.
by rewrite val_insubd /= (leq_ltn_trans (leq_pred _) (ltn_ord k)).
Qed.

Lemma bd_placeP1_cell (c : cellN) j :
  (forall l, (val l <= val j)%N -> c l = Vtx None) ->
  bd (consP j (cc c)) = topcoord j (cc c) - cc c - consP j (bd (cc c)).
Proof.
move=> hc; rewrite consP_cc bd_sum topcoord_cc bd_cc.
have splitj k : bd1 (setc c j (Edg (k, p1)))
  = edgeterm (setc c j (Edg (k, p1))) j
    + \sum_(i | i != j) edgeterm (setc c j (Edg (k, p1))) i.
  by rewrite /bd1 (bigD1 j).
under eq_bigr => k _ do rewrite bd_cc (splitj R k).
rewrite big_split /=.
have Hj : \sum_(k : 'I_n) edgeterm (setc c j (Edg (k, p1))) j
        = cc (setc c j (Vtx topv)) - cc c :> chain.
  rewrite -edge_telescope; last exact: (hc j (leqnn _)).
  apply: eq_bigr => k _; rewrite /edgeterm ffunE eqxx.
  have -> : rk (setc c j (Edg (k, p1))) j = 0.
    apply/eqP; rewrite cards_eq0; apply/eqP/setP => l; rewrite !inE ffunE.
    case: (eqVneq l j) => [->|lj]; first by rewrite ltnn andbF.
    by have [hlj|hlj] := ltnP (val l) (val j); [rewrite (hc l (ltnW hlj))|rewrite andbF].
  by rewrite /Edg /= expr0 scale1r !fvj /etop /ebot.
rewrite Hj; congr (_ + _).
rewrite exchange_big /=.
have ecj : edgeterm c j = 0 :> chain by rewrite /edgeterm (hc j (leqnn _)).
have bd1E : bd1 c = \sum_(i0 : 'I_N | i0 != j) edgeterm c i0 :> chain.
  by rewrite /bd1 (bigD1 j) //= ecj add0r.
rewrite bd1E (big_morph (consP j) (consPD j) (consP0 j)) -sumrN.
apply: eq_bigr => i0 i0j.
case E : (c i0) => [v|kr].
  rewrite /edgeterm E consP0 oppr0 big1 // => k _.
  by rewrite /edgeterm ffunE (negbTE i0j) E.
have ji0 : (val j < val i0)%N.
  by have := hc i0; rewrite E; case: (ltnP (val i0) (val j).+1) => [hle /(_ hle)//|].
under eq_bigr => k _.
  rewrite /edgeterm ffunE (negbTE i0j) E (rk_setc_below k hc ji0).
  rewrite (fv_setc_comm _ _ _ i0j) (fv_setc_comm _ _ _ i0j).
  over.
rewrite -scaler_sumr sumrB -!consP_cc -consPB exprS mulN1r scaleNr -consPZ.
by congr (- consP j _); rewrite /edgeterm E.
Qed.

Lemma bd_placeP1 j x :
  below j x -> bd (consP j x) = topcoord j x - x - consP j (bd x).
Proof.
move=> hb; rewrite {1}[x]chain_decomp.
rewrite (big_morph (consP j) (consPD j) (consP0 j)).
under eq_bigr => c _ do rewrite consPZ.
rewrite (big_morph bd (fun a b => @bdD n p N R a b) (_ : bd 0 = 0)); last by rewrite /bd lin0.
under eq_bigr => c _ do rewrite bdZ.
have Etop : topcoord j x = \sum_c x c *: topcoord j (cc c).
  rewrite {1}[x]chain_decomp (big_morph (topcoord j) (topcoordD j) (_ : topcoord j 0 = 0));
    last by rewrite /topcoord lin0.
  by apply: eq_bigr => c _; rewrite topcoordZ.
have Ecp : consP j (bd x) = \sum_c x c *: consP j (bd (cc c)).
  rewrite {1}[x]chain_decomp (big_morph bd (fun a b => @bdD n p N R a b) (_ : bd 0 = 0));
    last by rewrite /bd lin0.
  rewrite (big_morph (consP j) (consPD j) (consP0 j)).
  by apply: eq_bigr => c _; rewrite bdZ consPZ.
rewrite Etop Ecp [X in _ = _ - X - _](chain_decomp x) -!sumrB /=.
apply: eq_bigr => c _; rewrite -!scalerBr.
have [->|xc] := eqVneq (x c) 0; first by rewrite !scale0r.
by rewrite bd_placeP1_cell // => l hl; apply: (hb c xc).
Qed.

Lemma h_alt d : (d < N)%N ->
  h d = topcoord (pc d) (htil d) - consP (pc d) (bd (htil d)).
Proof.
move=> dN; rewrite /h bd_placeP1; last exact: below_htil.
by rewrite [_ - _ - _]addrAC addrNK.
Qed.

(** coverage: some coordinate is a full-path top vertex (n,r). *)
Definition covered (c : cellN) : bool :=
  [exists j : 'I_N, [exists r : 'I_p, c j == Vtx (Some (topk, r))]].
Definition coveredX (X : chain) : Prop := forall c, X c != 0 -> covered c.

Lemma coveredX_D x y : coveredX x -> coveredX y -> coveredX (x + y).
Proof.
move=> hx hy c; rewrite ffunE => hc.
have [xc|xc] := eqVneq (x c) 0; last by apply: hx.
by apply: hy; move: hc; rewrite xc add0r.
Qed.

Lemma coveredX0 : coveredX 0.
Proof. by move=> c; rewrite ffunE eqxx. Qed.

Lemma coveredX_sum (I : Type) (r : seq I) (F : I -> chain) :
  (forall k, coveredX (F k)) -> coveredX (\sum_(k <- r) F k).
Proof. by move=> hF; elim/big_rec: _ => [|k a _ hb]; [exact: coveredX0|exact: coveredX_D]. Qed.

Lemma covered_shift c : covered c -> covered (shift c).
Proof.
move=> /existsP[j /existsP[r /eqP hj]].
apply/existsP; exists j; apply/existsP; exists (shiftp r).
by rewrite ffunE hj.
Qed.

Lemma coveredX_nu x : coveredX x -> coveredX (nu x).
Proof. by move=> hx d /lin_cc_supp[c xc <-]; apply/covered_shift/hx. Qed.

Lemma coveredX_nupow r x : coveredX x -> coveredX (nupow r x).
Proof.
by move=> hx; elim: r => [//|r IH]; rewrite /nupow iterS -/(nupow r x); apply: coveredX_nu.
Qed.

Lemma coveredX_sigma x : coveredX x -> coveredX (sigma x).
Proof. by move=> hx; rewrite /sigma; apply: coveredX_sum => r; apply: coveredX_nupow. Qed.

Lemma coveredX_N x : coveredX x -> coveredX (- x).
Proof.
move=> hx c; rewrite ffunE => hc; apply: hx.
by apply: contra hc => /eqP ->; rewrite oppr0.
Qed.

Lemma coveredX_opd d x : coveredX x -> coveredX (opd d x).
Proof.
rewrite /opd; case: (odd d); last exact: coveredX_sigma.
move=> hx; apply: coveredX_D; [exact: coveredX_nu|exact: coveredX_N].
Qed.

Lemma covered_setc_topv c j : covered (setc c j (Vtx topv)).
Proof.
apply/existsP; exists j; apply/existsP; exists p1.
by rewrite ffunE eqxx /topv.
Qed.

Lemma coveredX_topcoordX j x : coveredX (topcoord j x).
Proof.
move=> d /lin_cc_supp[c _ <-]; exact: covered_setc_topv.
Qed.

Lemma covered_consP j (c : cellN) : covered c -> c j = Vtx None ->
  forall k, covered (setc c j (Edg (k, p1))).
Proof.
move=> /existsP[j' /existsP[r /eqP hj']] cj k.
have j'j : j' != j by apply/eqP => e; move: hj'; rewrite e cj.
apply/existsP; exists j'; apply/existsP; exists r.
by rewrite ffunE (negbTE j'j) hj'.
Qed.

Lemma lin_sum_fun (I : Type) (rr : seq I) (g : I -> cellN -> chain) x :
  lin (fun c => \sum_(k <- rr) g k c) x = \sum_(k <- rr) lin (g k) x.
Proof.
rewrite /lin exchange_big /=; apply: eq_bigr => c _.
by rewrite scaler_sumr.
Qed.

Lemma coveredX_consP j x : coveredX x ->
  (forall c, x c != 0 -> c j = Vtx None) -> coveredX (consP j x).
Proof.
move=> hx hj; rewrite /consP lin_sum_fun; apply: coveredX_sum => k.
move=> d /lin_cc_supp[c xc <-].
by apply: covered_consP; [exact: hx | exact: hj].
Qed.

Lemma bd_htil_covered d : (d < N)%N -> coveredX (bd (htil d)).
Proof.
elim: d => [_|d IH dN].
  rewrite /= bd_cc /bd1 big1 => [|i _]; first exact: coveredX0.
  by rewrite /edgeterm /o_cell ffunE.
have key : bd (htil d.+1)
         = opd d (topcoord (pc d) (htil d)) - opd d (consP (pc d) (bd (htil d))).
  have -> : htil d.+1 = opd d (consP (pc d) (htil d)) by rewrite /opd /=; case: (odd d).
  rewrite bd_opd bd_placeP1; last exact/below_htil/ltnW.
  by rewrite !opdB opd_kills_htil subr0.
rewrite key; apply: coveredX_D; last apply: coveredX_N.
- by apply: coveredX_opd; exact: coveredX_topcoordX.
- apply: coveredX_opd; apply: coveredX_consP; first by apply: IH; apply: ltnW.
  by move=> cc0 hc0; apply: (below_bd (below_htil (ltnW dN)) hc0).
Qed.

(** K-membership via vertex selections. *)
Definition vsel (c : cellN) (T : {set 'I_N}) : {ffun 'I_N -> cut} :=
  [ffun i => match c i with
             | inl v => v
             | inr kr => if i \in T then Some kr else slide (Some kr)
             end].
Definition inK (c : cellN) : bool := [forall T, inX (vsel c T)].

Lemma covered_inK c : covered c -> inK c.
Proof.
move=> /existsP[j /existsP[r /eqP hj]]; apply/forallP => T; apply/forallP => b.
apply/existsP; exists j; rewrite /vsel ffunE hj /covers /= /topk /=.
by rewrite subn1 -ltnS prednK // ltn_ord.
Qed.

Lemma h_inK d : (d < N)%N -> forall c, (h d) c != 0 -> inK c.
Proof.
move=> dN c hc; apply: covered_inK; move: c hc.
have : coveredX (h d); last by [].
rewrite h_alt //; apply: coveredX_D; last apply: coveredX_N.
- exact: coveredX_topcoordX.
- apply: coveredX_consP; first exact: bd_htil_covered.
  by move=> cc0 hc0; apply: (below_bd (below_htil dN) hc0).
Qed.

(** Meunier's indexed forms of the boundary relations. *)
Lemma hrel_odd l : bd (h (2 * l).+1) = sigma (h (2 * l)).   (* ∂h_{2l+1} = Σ_r ν^r h_{2l} *)
Proof. by have := hrel (2 * l); rewrite /opd mul2n odd_double. Qed.

Lemma hrel_even l : bd (h (2 * l).+2) = nu (h (2 * l).+1) - h (2 * l).+1.
Proof. by have := hrel (2 * l).+1; rewrite /opd /= mul2n odd_double. Qed.

End Hemi.
