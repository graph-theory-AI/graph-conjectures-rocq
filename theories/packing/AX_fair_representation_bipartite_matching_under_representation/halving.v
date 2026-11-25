(** * Halving a set of edges of a bipartite graph

    The edges of a bipartite multigraph are the elements of a finite type [T], and the two ends of
    each edge are given by [u, v : T -> nat].  More precisely, [u] and [v] are injective on the set
    [X] of edges under consideration: the edges at a vertex [a] have distinct codes [u x] with
    [u x %/ 2 ^ L = a].  Lemma [halving]: there is a subset [Y] of [X] such that [u./2] and [v./2]
    are injective on [Y], and that contains half of the edges of each set A_0, ..., A_(t-1), up to
    a constant that depends only on [t].  Hence the degrees can be divided by 2 ^ L, up to a
    constant which does not depend on [L] ([halving_iter]).

    Two edges of [X] are in conflict if they have the same [u./2], or the same [v./2].
    1. There is a 2-colouring of [X] such that edges in conflict have distinct colours
       ([conflict_coloring]), because the conflict graph consists of paths and even cycles.
    2. There is an enumeration of [X] such that, for each cut, at most two conflicts go across the
       cut ([layout]).
    3. By the splitting lemma, the colouring becomes balanced in each set A_j when the colours are
       flipped in some intervals of this enumeration.  Only the conflicts that go across one of
       the [t] cuts may be violated, and [Y] is a colour class minus an end of each of these. *)

From mathcomp Require Import boot.
From GC.packing.AX_fair_representation_bipartite_matching_under_representation
  Require Import splitting.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Conflicts and their 2-colouring *)

(** The other number with the same half. *)
Definition twin (n : nat) : nat := ~~ odd n + n./2.*2.

Lemma odd_twin n : odd (twin n) = ~~ odd n.
Proof. by rewrite oddD odd_double addbF oddb. Qed.

Lemma twinK : involutive twin.
Proof. by move=> n; rewrite {1}/twin odd_twin half_bit_double negbK odd_double_half. Qed.

Lemma twin_neq n : twin n != n.
Proof. by apply/eqP => eq_n; have := odd_twin n; rewrite eq_n; case: odd. Qed.

Lemma half_eq m n : m./2 = n./2 -> m = n \/ m = twin n.
Proof.
move=> eq_h; rewrite /twin -[m]odd_double_half -[X in _ = X \/ _]odd_double_half eq_h.
by case: (odd m) (odd n) => [] []; auto.
Qed.

Section Conflicts.
Variable T : finType.
Implicit Types (X Y : {set T}) (u v : T -> nat).

Definition conflict u v : rel T := [rel x y | (u y == twin (u x)) || (v y == twin (v x))].

Lemma conflict_sym u v : symmetric (conflict u v).
Proof. by move=> x y /=; congr (_ || _); rewrite eq_sym (inv_eq twinK). Qed.

(** By induction on [X]: if [x] and [y] have the same [u./2], then they are removed and the other
    elements with the same [v./2] as [x] and as [y] become in conflict. *)
Lemma conflict_coloring u v X :
  {in X &, injective u} -> {in X &, injective v} ->
  exists c : pred T, {in X &, forall x y, conflict u v x y -> c x != c y}.
Proof.
move=> inj_u; have [n le_n] := ubnP #|X|; elim: n X v le_n inj_u => // n IH X v le_n inj_u inj_v.
have [/exists_inP[x xX /exists_inP[y yX /eqP uy]] | no_u] :=
  boolP [exists x in X, [exists y in X, u y == twin (u x)]]; last first.
  exists (fun x => odd (v x)) => x y xX yX /orP[/eqP uy | /eqP->]; last first.
    by rewrite odd_twin; case: odd.
  case/exists_inP: no_u; exists x => //; apply/exists_inP; exists y => //; exact/eqP.
have ne_xy : x != y by apply: contraTneq (twin_neq (u x)) => eq_xy; rewrite -uy eq_xy eqxx.
pose X' := X :\ x :\ y; pose v' z := if v z == twin (v x) then v y else v z.
have X'X z : z \in X' -> [/\ z \in X, z != x & z != y] by rewrite !inE => /and3P[].
have [c' c'P] : exists c' : pred T, {in X' &, forall z w, conflict u v' z w -> c' z != c' w}.
  apply: IH => [| z w /X'X[zX _ _] /X'X[wX _ _] | z w /X'X[zX _ zy] /X'X[wX _ wy]].
  - rewrite (cardsD1 x X) xX ltnS in le_n; apply: leq_trans le_n.
    by rewrite ltnS subset_leq_card ?subsetDl.
  - exact: inj_u.
  rewrite /v'; case: eqP => [vz | _]; case: eqP => [vw | _]; last exact: inj_v.
  - by move=> _; apply: inj_v => //; rewrite vz vw.
  - by move/inj_v => eq; rewrite eq ?eqxx in wy.
  - by move/inj_v => eq; rewrite eq ?eqxx in zy.
pose b := if [pick z in X' | v z == twin (v x)] is Some z then ~~ c' z else
          if [pick z in X' | v z == twin (v y)] is Some z then c' z else true.
pose c z := if z == x then b else if z == y then ~~ b else c' z.
have cE z : z \in X' -> c z = c' z by case/X'X=> _ /negPf zx /negPf zy; rewrite /c zx zy.
have cx : c x = b by rewrite /c eqxx.
have cy : c y = ~~ b by rewrite /c eq_sym (negPf ne_xy) eqxx.
have in_X' z : z \in X -> [\/ z = x, z = y | z \in X'].
  move=> zX; rewrite !inE zX andbT.
  case: eqP => [->|_]; first by constructor 2.
  by case: eqP => [->|_]; [constructor 1 | constructor 3].
have cPx z : z \in X -> conflict u v x z -> c x != c z.
  move=> zX /orP[/eqP uz | /eqP vz].
    by rewrite (inj_u z y) ?uz // cx cy; case: (b).
  have [zx | zy | zX'] := in_X' z zX; first by move: (twin_neq (v x)); rewrite -vz zx eqxx.
    by rewrite zy cx cy; case: (b).
  rewrite cx cE // /b; case: pickP => [w /andP[/X'X[wX _ _] /eqP vw] | /(_ z)].
    by rewrite (inj_v z w) ?vw //; case: (c' w).
  by rewrite zX' vz eqxx.
have cPy z : z \in X -> conflict u v y z -> c y != c z.
  move=> zX /orP[/eqP uz | /eqP vz].
    by rewrite (inj_u z x) ?uz ?uy ?twinK // cx cy; case: (b).
  have [zx | zy | zX'] := in_X' z zX; first by rewrite zx cx cy; case: (b).
    by move: (twin_neq (v y)); rewrite -vz zy eqxx.
  rewrite cy cE // /b; case: pickP => [w /andP[wX' /eqP vw] | no_w].
    rewrite negbK c'P //=; apply/orP; right; rewrite /v' vw eqxx vz (inj_eq (inv_inj twinK)).
    by rewrite (inj_in_eq inj_v) // [y == x]eq_sym (negPf ne_xy).
  case: pickP => [w /andP[/X'X[wX _ _] /eqP vw] | /(_ z)].
    by rewrite (inj_v z w) ?vw //; case: (c' w).
  by rewrite zX' vz eqxx.
exists c => z w zX wX czw.
have [zx | zy | zX'] := in_X' z zX; first by rewrite zx in czw *; exact: cPx.
  by rewrite zy in czw *; exact: cPy.
have [wx | wy | wX'] := in_X' w wX.
- by rewrite wx conflict_sym in czw *; rewrite eq_sym; exact: cPx.
- by rewrite wy conflict_sym in czw *; rewrite eq_sym; exact: cPy.
rewrite !cE //; apply: c'P => //; case/orP: czw => [uw | /eqP vw]; apply/orP; [by left | right].
have [_ zx _] := X'X z zX'; have [_ wx _] := X'X w wX'.
rewrite /v' vw (inj_eq (inv_inj twinK)) (inj_in_eq inj_v) // (negPf zx).
case: (v z =P twin (v x)) => [vz | _]; last by rewrite eqxx.
rewrite vz twinK in vw.
by rewrite (inj_v _ _ wX xX vw) eqxx in wx.
Qed.

End Conflicts.

(** ** Enumeration with at most two conflicts across each cut *)

Section Layout.
Variables (T : eqType) (e : rel T).
Hypothesis e_sym : symmetric e.

(** The number of pairs of [P * Q] in the relation [e]. *)
Definition cross (P Q : seq T) : nat := \sum_(x <- P) count (e x) Q.

Lemma cross_sym P Q : cross P Q = cross Q P.
Proof.
have crossE P' Q' : cross P' Q' = \sum_(x <- P') \sum_(y <- Q') (e x y : nat).
  by apply: eq_bigr => x _; rewrite -sum1_count big_mkcond; apply: eq_bigr => y _; case: (e x y).
rewrite !crossE exchange_big /=; apply: eq_bigr => y _; apply: eq_bigr => x _.
by rewrite e_sym.
Qed.

(** The sequence is built greedily: the next element is related to a preceding one if possible. *)
Lemma layout P Q :
  cross P Q <= 2 -> {in Q, forall x, count (e x) (P ++ Q) <= 2} ->
  exists2 s, perm_eq s Q & forall n, cross (P ++ take n s) (drop n s) <= 2.
Proof.
have [n] := ubnP (size Q); elim: n P Q => // n IH P Q le_n le_c le_e.
have [Q0 | Q_neq0] := eqVneq Q [::].
  by rewrite Q0 in le_c *; exists [::] => // -[|n'] /=; rewrite cats0.
have [y yQ y_adj] : exists2 y, y \in Q & (cross P Q == 0) || (0 < count (e y) P).
  have [c0 | c_neq0] := eqVneq (cross P Q) 0.
    by case: (Q) Q_neq0 => // x Q' _; exists x; rewrite ?mem_head.
  apply/hasP; apply: contraNT c_neq0 => /hasPn no_y; rewrite cross_sym /cross big1_seq // => y yQ.
  by apply/eqP; rewrite -leqn0 leqNgt no_y.
have eq_Q := perm_to_rem yQ; set Q' := rem y Q in eq_Q.
have crossE : cross P Q = count (e y) P + cross P Q'.
  by rewrite cross_sym /cross (perm_big _ eq_Q) big_cons /= -/(cross Q' P) cross_sym.
have [||x xQ'|s eq_s cross_s] := IH (rcons P y) Q'.
- by rewrite (perm_size eq_Q) in le_n.
- have -> : cross (rcons P y) Q' = cross P Q' + count (e y) Q'.
    by rewrite /cross -cats1 big_cat big_seq1.
  have le_y : count (e y) P + count (e y) Q' <= 2.
    apply: leq_trans (le_e y yQ); rewrite count_cat (permP eq_Q) leq_add2l; exact: leq_addl.
  rewrite crossE in le_c y_adj; case/orP: y_adj => [|y0].
    by rewrite addn_eq0 => /andP[/eqP y0 /eqP->]; rewrite y0 in le_y.
  rewrite -(leq_add2l 2); apply: leq_trans (leq_add le_c le_y); rewrite addnACA leq_add2r.
  by rewrite addnn (leq_double 1).
- rewrite cat_rcons; apply: leq_trans (le_e x _); last exact: mem_rem xQ'.
  by rewrite !count_cat (permP eq_Q).
have eq_yQ : perm_eq (y :: s) Q by rewrite (permPr eq_Q) perm_cons.
exists (y :: s) => // -[|m]; last by rewrite /= -cat_rcons.
by rewrite take0 drop0 cats0 /cross (eq_bigr _ (fun x _ => permP eq_yQ (e x))).
Qed.

End Layout.

(** ** The halving lemma *)

(** The error on the size of [t] sets. *)
Definition err (t : nat) : nat := t * t.*2.+1 + (t.*2 + t.*2).

Section Halving.
Variables (T : finType) (t : nat) (A : nat -> {set T}).
Implicit Types (X Y : {set T}) (u v : T -> nat).

Lemma halving u v X :
  {in X &, injective u} -> {in X &, injective v} ->
  exists Y, [/\ Y \subset X, {in Y &, injective (half \o u)}, {in Y &, injective (half \o v)} &
    forall j, j < t -> #|X :&: A j| <= #|Y :&: A j|.*2 + err t /\
                       #|Y :&: A j|.*2 <= #|X :&: A j| + err t].
Proof.
move=> inj_u inj_v; have [c cP] := conflict_coloring inj_u inj_v.
set e := conflict u v in cP; have e_sym : symmetric e := conflict_sym u v.
have count1 (w : T -> nat) a : {in X &, injective w} -> count (fun y => w y == a) (enum X) <= 1.
  move=> inj_w; rewrite -(count_map w (pred1 a)) count_uniq_mem ?leq_b1 //.
  rewrite map_inj_in_uniq ?enum_uniq // => x y; rewrite !mem_enum; exact: inj_w.
have [|x _|s eq_s cross_s] := layout e_sym (P := [::]) (Q := enum X).
- by rewrite /cross big_nil.
- apply: leq_trans (leq_add (count1 u (twin (u x)) inj_u) (count1 v (twin (v x)) inj_v)).
  by rewrite -count_predUI leq_addr.
have uniq_s : uniq s by rewrite (perm_uniq eq_s) enum_uniq.
have mem_s x : (x \in s) = (x \in X) by rewrite (perm_mem eq_s) mem_enum.
have [f [B [sz_B fB bal]]] := splitting t (fun j => mem (A j)) c uniq_s.
pose g x := f (index x s) (+) c x.
pose bad := [set x in X | [exists y in X, [&& e x y, index x s <= index y s &
                                            f (index x s) != f (index y s)]]].
pose Y := [set x in X | g x] :\: bad.
have YP x y : x \in Y -> y \in Y -> ~~ e x y.
  wlog le_xy : x y / index x s <= index y s => [IH xY yY|].
    by case/orP: (leq_total (index x s) (index y s)) => /IH; [|rewrite e_sym]; exact.
  rewrite !inE => /andP[nbad /andP[xX gx]] /andP[_ /andP[yX gy]].
  apply: contra nbad => exy; rewrite xX /=; apply/exists_inP; exists y; rewrite // exy le_xy /=.
  by move: (cP x y xX yX exy) gx gy; rewrite /g; case: (c x) (c y) (f _) (f _) => [] [] [] [].
have YX : Y \subset X by apply/subsetP => x; rewrite !inE => /and3P[].
pose badl b := [seq x <- take b s | has (e x) (drop b s)].
have le_bad : #|bad| <= t.*2.
  have sz_badl b : size (badl b) <= 2.
    apply: leq_trans (cross_s b); rewrite size_filter -sum1_count big_mkcond leq_sum //= => x _.
    by rewrite has_count; case: count.
  apply: leq_trans (_ : size (flatten [seq badl b | b <- B]) <= _).
    rewrite cardE; apply: uniq_leq_size (enum_uniq _) _ => x; rewrite mem_enum inE.
    case/andP=> xX /exists_inP[y yX /and3P[exy le_xy /(fB _ _ le_xy)/hasP[b bB /andP[lt_x le_y]]]].
    apply/flatten_mapP; exists b => //; rewrite mem_filter in_take ?mem_s // lt_x andbT.
    apply/hasP; exists y => //; have : y \in take b s ++ drop b s by rewrite cat_take_drop mem_s.
    by rewrite mem_cat in_take ?mem_s // ltnNge le_y.
  apply: leq_trans (_ : (size B).*2 <= _); last by rewrite leq_double.
  by elim: (B) => //= b B' IH; rewrite size_cat doubleS -addn2 addnC leq_add.
exists Y; split=> // [x y xY yY|x y xY yY|j lt_j].
- case/half_eq=> [|uy]; first exact: inj_u (subsetP YX _ xY) (subsetP YX _ yY).
  by have := YP y x yY xY; rewrite /e /conflict /= uy eqxx.
- case/half_eq=> [|vy]; first exact: inj_v (subsetP YX _ xY) (subsetP YX _ yY).
  by have := YP y x yY xY; rewrite /e /conflict /= vy eqxx orbT.
set S := X :&: A j; pose G := [set x | g x].
have le_Y : #|Y :&: A j| <= #|S :&: G|.
  by apply/subset_leq_card/subsetP => x; rewrite !inE => /andP[/and3P[_ -> ->] ->].
have le_S : #|S :&: G| <= #|Y :&: A j| + t.*2.
  apply: leq_trans (leq_add (leqnn _) le_bad); apply: leq_trans (leq_card_setU _ _).
  apply/subset_leq_card/subsetP => x xSG; rewrite in_setU orbC; case: (boolP (x \in bad)) => //= nb.
  by rewrite in_setI in_setD nb; move: xSG; rewrite !inE => /andP[/andP[-> ->] ->].
have countE P : #|[set x in X | P x]| = count P s.
  rewrite (permP eq_s) -size_filter.
  have /card_uniqP<- : uniq (filter P (enum X)) by rewrite filter_uniq ?enum_uniq.
  by apply: eq_card => x; rewrite !inE mem_filter mem_enum andbC.
pose size_of b := count (fun x => (x \in A j) && (g x == b)) s.
have balE b : size_of b <= size_of (~~ b) + t * t.*2.+1.
  have := bal j b lt_j; congr (_ <= _ + _).
  by apply: eq_count => x; rewrite /g /=; case: (b) (_ (+) _) => [] [].
have SG : #|S :&: G| = size_of true.
  by rewrite /size_of -countE; apply: eq_card => x; rewrite !inE eqb_id andbA.
have SG' : #|S :\: G| = size_of false.
  by rewrite /size_of -countE; apply: eq_card => x; rewrite !inE eqbF_neg andbC andbA.
have le1 := balE true; have le2 := balE false; rewrite -SG -SG' in le1 le2.
rewrite -(cardsID G S) -addnn; split.
  apply: leq_trans (leq_add le_S (leq_trans le2 (leq_add le_S (leqnn _)))) _.
  by rewrite addnA addnACA -(addnA (_ + _)) leq_add2l addnC.
apply: leq_trans (leq_add le_Y (leq_trans le_Y le1)) _.
by rewrite addnA leq_add2l leq_addr.
Qed.

(** Repeated halving divides the degrees and the sizes of the sets by [2 ^ L]. *)
Lemma halving_iter L u v X :
  {in X &, injective u} -> {in X &, injective v} ->
  exists Y, [/\ Y \subset X, {in Y &, injective (fun x => u x %/ 2 ^ L)},
    {in Y &, injective (fun x => v x %/ 2 ^ L)} &
    forall j, j < t -> #|X :&: A j| + err t <= 2 ^ L * (#|Y :&: A j| + err t) /\
                       2 ^ L * #|Y :&: A j| + err t <= #|X :&: A j| + 2 ^ L * err t].
Proof.
elim: L u v X => [|L IH] u v X inj_u inj_v.
  exists X; split=> // [x y xX yX | x y xX yX | j _]; rewrite ?expn0 ?divn1 ?mul1n ?leqnn //.
  - exact: inj_u.
  - exact: inj_v.
have [Y [YX inj_uY inj_vY hY]] := halving inj_u inj_v.
have [Z [ZY inj_uZ inj_vZ hZ]] := IH _ _ _ inj_uY inj_vY.
have divE a : a./2 %/ 2 ^ L = a %/ 2 ^ L.+1 by rewrite -divn2 -divnMA expnS.
exists Z; split=> [|x y xZ yZ|x y xZ yZ|j lt_j]; first exact: subset_trans YX.
- by rewrite -!divE; exact: inj_uZ.
- by rewrite -!divE; exact: inj_vZ.
have [le1 le2] := hY j lt_j; have [le1' le2'] := hZ j lt_j.
rewrite expnS -!mulnA !mul2n; split.
  apply: leq_trans (_ : _ <= (#|Y :&: A j| + err t).*2) _; last by rewrite leq_double.
  by rewrite doubleD -[(err t).*2]addnn addnA leq_add2r.
rewrite -(leq_add2r (err t)) -addnA addnn -doubleD addnAC.
apply: leq_trans (_ : (#|Y :&: A j| + 2 ^ L * err t).*2 <= _); first by rewrite leq_double.
by rewrite doubleD leq_add2r.
Qed.

End Halving.
