(** * Splitting a sequence into two parts with few cuts

    Lemma [splitting]: given a sequence [s] of distinct elements, [t] sets A_0, ..., A_(t-1) and a
    2-colouring [c] of the elements, it is possible to flip the colours in some intervals of [s],
    with at most [t] cuts between flipped and unflipped positions, such that the two colours are
    balanced in each set A_j, up to t * (2t+1) elements.  This is an approximate form of the
    theorem on the splitting of a necklace between two thieves (Goldberg and West, Alon), and it
    follows from Tucker's lemma in the same way. *)

From mathcomp Require Import boot.
From GC.GraphLib Require Import tucker.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** The sign sequence of a point of the grid *)

Section Signs.
Variable N : nat.

(** A coordinate [s] in [0, 2N] encodes an interval of [|s - N|] positions, whose sign is that of
    [s - N].  A point is a sequence of consecutive intervals: the sign of the positions after them
    is [e], and the positions after the first [N] ones are irrelevant. *)
Definition len (s : nat) : nat := (s - N) + (N - s).

Fixpoint sign (e : bool) (x : seq nat) (p : nat) : bool :=
  if x is s :: x' then if p < len s then N < s else sign e x' (p - len s) else e.

(** The ends of the intervals, when the first one begins at [a]. *)
Fixpoint ends (a : nat) (x : seq nat) : seq nat :=
  if x is s :: x' then (a + len s) :: ends (a + len s) x' else [::].

Lemma size_ends a x : size (ends a x) = size x.
Proof. by elim: x a => //= s x IH a; rewrite IH. Qed.

(** If two positions have distinct signs, there is an end between them. *)
Lemma ends_sign e x a p q :
  p <= q -> sign e x p != sign e x q -> has (fun b => a + p < b <= a + q) (ends a x).
Proof.
elim: x a p q => [|s x IH] a p q pq /=; first by rewrite eqxx.
rewrite ltn_add2l leq_add2l; case: (ltnP p) => [lt_p | le_p].
  by case: (ltnP q) => // _; rewrite eqxx.
have le_q := leq_trans le_p pq; rewrite ltnNge le_q /= => /(IH (a + len s) _ _ (leq_sub2r _ pq)).
by rewrite -!(addnA a) (subnKC le_p) (subnKC le_q).
Qed.

(** ** Dependence on the point *)

Lemma len_close s s' : s <= s'.+1 -> s' <= s.+1 -> len s <= (len s').+1.
Proof.
move=> le_s le_s'; rewrite /len; case: (leqP s N) => [le_sN | /ltnW le_Ns].
  move: (le_sN); rewrite -subn_eq0 => /eqP->; rewrite add0n -addnS.
  apply: leq_trans (leq_addl _ _); rewrite leq_subLR addnS.
  by apply: leq_trans (leq_add le_s' (leqnn _)); rewrite -leq_subLR.
move: (le_Ns); rewrite -subn_eq0 => /eqP->; rewrite addn0 -addSn.
apply: leq_trans (leq_addr _ _); rewrite leq_subLR addnS.
by apply: (leq_trans le_s); rewrite ltnS -leq_subLR.
Qed.

Lemma sign_len_close s s' :
  s <= s'.+1 -> s' <= s.+1 -> 0 < len s -> 0 < len s' -> (N < s) = (N < s').
Proof.
wlog lt_s : s s' / s < s' => [IH le_s le_s' s0 s'0|].
  by case: (ltngtP s s') => [lt_s | lt_s | ->] //; [|apply/esym]; exact: IH.
move=> _ le_s'; have -> : s' = s.+1 by apply/eqP; rewrite eqn_leq le_s'.
rewrite /len ltnS; case: (ltngtP N s) => // <-; by rewrite subnn.
Qed.

(** The signs of close positions of close points are equal, except near the ends. *)
Lemma sign_close e x y a p q d :
  close x y -> p <= q + d -> q <= p + d -> sign e x p != sign e y q ->
  has (fun b => (b <= a + p + (d + size x)) && (a + p <= b + (d + size x))) (ends a x).
Proof.
elim: x y a p q d => [|s x IH] [|s' y] a p q d //=; first by rewrite eqxx.
case/andP=> /andP[le_s le_s'] cl pq qp.
have le_l := len_close le_s le_s'; have le_l' := len_close le_s' le_s.
case: (ltnP p) => [lt_p | le_p]; case: (ltnP q) => [lt_q | le_q].
- rewrite (sign_len_close le_s le_s') ?eqxx //; first exact: leq_ltn_trans lt_p.
  exact: leq_ltn_trans lt_q.
- move=> _; apply/orP; left; rewrite -!(addnA a) !leq_add2l.
  rewrite (leq_trans (ltnW lt_p)) ?leq_addr // andbT addnA addnS (leq_trans le_l) // ltnS.
  by rewrite (leq_trans le_q) // (leq_trans qp) // leq_addr.
- move=> _; apply/orP; left; rewrite -!(addnA a) !leq_add2l (leq_trans le_p) ?leq_addr //=.
  by rewrite (leq_trans pq) // leq_add ?leq_addr // -ltnS (leq_trans lt_q).
move=> ne; apply/orP; right.
have := IH y (a + len s) (p - len s) (q - len s') d.+1 cl _ _ ne.
rewrite -(addnA a) (subnKC le_p) addSnnS; apply.
  rewrite leq_subLR addnA addnS -addSn (leq_trans pq) // leq_add2r.
  by rewrite -{1}(subnKC le_q) -addSn leq_add2r.
rewrite leq_subLR addnA addnS -addSn (leq_trans qp) // leq_add2r.
by rewrite -{1}(subnKC le_p) -addSn leq_add2r.
Qed.

(** The signs of close points are equal, except in a small number of positions. *)
Lemma count_sign_close e x y (l : seq nat) :
  close x y -> uniq l ->
  count (fun p => sign e x p != sign e y p) l <= size x * (size x).*2.+1.
Proof.
move=> cl uniq_l; rewrite -size_filter.
pose near := [seq (b - size x) + i | b <- ends 0 x, i <- iota 0 (size x).*2.+1].
have -> : size x * (size x).*2.+1 = size near by rewrite size_allpairs size_iota size_ends.
apply: uniq_leq_size => [|p]; first by rewrite filter_uniq.
rewrite mem_filter => /andP[ne _].
have /hasP[b bx /andP[]] := sign_close 0 cl (leq_addr 0 p) (leq_addr 0 p) ne.
rewrite !add0n => le_b le_p; apply/allpairsP; exists (b, p - (b - size x)); split=> //.
  rewrite mem_iota add0n ltnS leq_subLR -addnn addnA.
  by apply: (leq_trans le_p); rewrite leq_add2r addnC -leq_subLR.
by rewrite subnKC // leq_subLR addnC.
Qed.

(** ** Extreme, shifted and symmetric points *)

Lemma sign_extreme e e' x y y' p :
  extreme N.*2 x -> p < N -> sign e (x ++ y) p = sign e' (x ++ y') p.
Proof.
elim: x p => //= s x IH p; case/orP=> [ext_s | ext_x] lt_p; last first.
  by case: ifP => // _; apply: IH; rewrite // (leq_ltn_trans (leq_subr _ _)).
suff -> : p < len s by [].
case/orP: ext_s => /eqP->; first by rewrite /len subn0 ltn_addl.
by rewrite /len -addnn addnK ltn_addr.
Qed.

Lemma sign_rcons e x p s b :
  p < N -> (forall q, q < N -> sign e [:: s] q = b) -> sign e (rcons x s) p = sign b x p.
Proof.
move=> lt_p sb; elim: x p lt_p => [|s' x IH] p lt_p; first exact: sb.
by rewrite /=; case: ifP => // _; apply: IH; exact: leq_ltn_trans (leq_subr _ _) lt_p.
Qed.

Lemma sign_opposite e x p :
  all (leq^~ N.*2) x -> sign (~~ e) (map (subn N.*2) x) p = ~~ sign e x p.
Proof.
elim: x p => //= s x IH p /andP[le_s le_x].
have -> : len (N.*2 - s) = len s.
  rewrite /len -addnn; case: (leqP s N) => [le_sN | /ltnW le_Ns].
    by rewrite -addnBA // addKn subnDA subnn sub0n addn0 (eqP le_sN).
  have le_N : s - N <= N by rewrite leq_subLR addnn.
  by rewrite -subnBA // subKn // (eqP le_Ns) addn0 subnAC subnn sub0n.
case: ltnP => [lt_p | _]; last exact: IH.
rewrite ltn_subRL -addnn ltn_add2r -leqNgt ltn_neqAle andb_idl // => _.
by apply: contraTneq lt_p => ->; rewrite /len subnn.
Qed.

End Signs.

(** ** The splitting lemma *)

Lemma splitting (T : eqType) (s : seq T) (t : nat) (A : nat -> pred T) (c : pred T) :
  uniq s ->
  exists f : pred nat, exists B : seq nat,
  [/\ size B <= t,
      forall p q, p <= q -> f p != f q -> has (fun b => p < b <= q) B &
      forall j b, j < t ->
        count (fun z => A j z && (f (index z s) (+) c z == b)) s <=
        count (fun z => A j z && (f (index z s) (+) c z != b)) s + t * t.*2.+1].
Proof.
move=> uniq_s; pose K := t * t.*2.+1; pose N := size s.
pose h j x b := count (fun z => A j z && (sign N true x (index z s) (+) c z == b)) s.
pose balanced j x := (h j x true <= h j x false + K) && (h j x false <= h j x true + K).
have [/existsP[x /forallP bal] | nbal] :=
    boolP [exists x : {bseq t of 'I_N.*2.+1}, [forall j : 'I_t, balanced j (map val x)]].
  exists (sign N true (map val x)), (ends N 0 (map val x)); split=> [|p q pq|j b lt_j].
  - by rewrite size_ends size_map size_bseq.
  - by move/(ends_sign 0 pq).
  have /andP[balT balF] := bal (Ordinal lt_j).
  have hN : count (fun z => A j z && (sign N true (map val x) (index z s) (+) c z != b)) s =
      h j (map val x) (~~ b).
    by apply: eq_count => z /=; case: (b) (_ (+) _) => [] [].
  by rewrite hN; case: (b).
pose first x := find (predC (balanced^~ x)) (iota 0 t).
have unbal k x : k <= t -> point N.*2 k x -> has (predC (balanced^~ x)) (iota 0 t).
  move=> le_kt /andP[/eqP sz_x /allP le_x]; apply: contraNT nbal.
  rewrite has_predC negbK => /allP bal; apply/existsP.
  have sz : size [seq (inord a : 'I_N.*2.+1) | a <- x] <= t by rewrite size_map sz_x.
  exists (Bseq sz); apply/forallP => j /=; rewrite -map_comp map_id_in => [a ax|].
    by rewrite /= inordK // ltnS le_x.
  by apply: bal; rewrite mem_iota ltn_ord.
have first_lt k x : k <= t -> point N.*2 k x -> first x < t.
  by move=> le_kt /(unbal _ _ le_kt); rewrite has_find size_iota.
have first_bal k x : k <= t -> point N.*2 k x -> ~~ balanced (first x) x.
  move=> le_kt pt_x; have := nth_find 0 (unbal k x le_kt pt_x).
  by rewrite nth_iota // (first_lt k).
pose lab x := (first x, h (first x) x false < h (first x) x true).
have eq_lab x y : (forall p, p < N -> sign N true x p = sign N true y p) -> lab x = lab y.
  move=> eq_xy; have eq_h j b : h j x b = h j y b.
    by apply: eq_in_count => z zs /=; rewrite eq_xy ?index_mem.
  have eq_first : first x = first y by apply: eq_find => j; rewrite /= /balanced !eq_h.
  by rewrite /lab eq_first !eq_h.
exfalso; apply: (@tucker N.*2 t lab).
- exact: first_lt.
- move=> k x _ _; apply: eq_lab => p lt_p; apply: sign_rcons => // q lt_q /=.
  rewrite /len -addnn addnK ltn_addr //; move: lt_q; case: (N) => // n _.
  by rewrite addSn ltnS leq_addl.
- move=> k x lt_kt /andP[sz_x le_x]; set y := map _ x.
  have pt_y : point N.*2 k y.
    by rewrite /point size_map sz_x; apply/allP => a /mapP[a' _ ->]; exact: leq_subr.
  have eq_h j b : h j (rcons x 0) b = h j y (~~ b).
    apply: eq_in_count => z zs /=; rewrite (sign_rcons _ (b := false)) ?index_mem // => [q lt_q | ].
      by rewrite /= /len subn0 ltn_addl.
    rewrite -[sign _ true y _]negbK (sign_opposite false) //.
    by case: (sign _ _ _ _) (c z) b => [] [] [].
  have eq_first : first (rcons x 0) = first y.
    by apply: eq_find => j; rewrite /= /balanced !eq_h andbC.
  rewrite /lab eq_first !eq_h /opposite /= -leqNgt ltn_neqAle andb_idl // => _.
  apply: contra (first_bal k y (ltnW lt_kt) pt_y) => /eqP eq_hy.
  by rewrite /balanced eq_hy leq_addr.
- move=> x i j ext_x; apply: eq_lab => p lt_p; rewrite -!cats1; exact: sign_extreme.
move=> k x y le_kt pt_x pt_y cl_xy [eq_first].
have nbx := first_bal k x le_kt pt_x; have := first_bal k y le_kt pt_y.
rewrite -eq_first; move: nbx; set j := first x => nbx nby.
pose D := count (fun z => sign N true x (index z s) != sign N true y (index z s)) s.
have le_D : D <= K.
  rewrite -[D](count_map (index^~ s) (fun p => sign N true x p != sign N true y p)).
  have uniq_l : uniq (map (index^~ s) s).
    by rewrite map_inj_in_uniq // => z w; apply: (index_inj z).
  apply: leq_trans (count_sign_close _ _ cl_xy uniq_l) _.
  by case/andP: pt_x => /eqP-> _; rewrite leq_mul // ltnS leq_double.
have [le_xy le_yx] : (forall b, h j x b <= h j y b + K) /\ forall b, h j y b <= h j x b + K.
  split=> b; apply: leq_trans (leq_add (leqnn _) le_D); rewrite -count_predUI;
    apply: leq_trans (leq_addr _ _); apply: sub_count => z /=;
    by case: (A j z) (sign _ _ _ _) (sign _ _ _ _) (c z) b => [] [] [] [] [].
have absurd u v : h j u true <= h j v true + K -> h j v false <= h j u false + K ->
    ~~ balanced j u -> ~~ balanced j v -> h j u false < h j u true -> h j v false < h j v true.
  move=> leT leF nbu nbv lt_u; rewrite ltnNge; apply/negP => le_v; move: nbu nbv.
  rewrite /balanced (leq_trans (ltnW lt_u)) ?leq_addr // andbT (leq_trans le_v) ?leq_addr //=.
  rewrite -!ltnNge => /leq_trans/(_ leT) lt_uv /leq_trans/(_ leF) lt_vu.
  by have := ltn_trans lt_uv lt_vu; rewrite !ltn_add2r ltnn.
case: ltnP => [lt_x | le_x] /esym; first by rewrite (absurd x y).
by move/negbFE/(absurd y x (le_yx _) (le_xy _) nby nbx); rewrite ltnNge le_x.
Qed.
