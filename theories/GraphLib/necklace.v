(** * Alon's theorem on the splitting of necklaces

    A necklace of [n] beads of [t] types, with a multiple of [q] beads of each type, can be cut at
    t(q-1) places at most, such that the pieces are distributed between [q] thieves and each thief
    receives the same number of beads of each type (N. Alon, "Splitting necklaces", Advances in
    Mathematics 63 (1987)) [splitting_necklace_theorem].

    If q = p is prime, the proof follows F. Meunier, "Simplotopal maps and necklace splitting",
    Discrete Mathematics 323 (2014), with the Tucker lemma of zp_tucker.v.  The factors of a cell
    are cuts: the vertex at distance k on the path r is a cut before the bead k, with the thief r,
    and an edge is a cut that moves across a bead.  A bead is given to the thief of the first cut
    after it.  A cell thus gives a nonempty set [owners] of thieves to each bead, and a choice of
    one thief for each bead corresponds to a vertex of the cell.  For each type, the winner of a
    choice is the thief with the most beads of this type, ties being broken by the first bead.  The
    label of a cell is computed from the sets of winners of its choices: its first component is a
    barycentre in Z_p of the first set that is not full, where p prime is used, and its second
    component is the sum of the sizes of the sets minus one.  By the Tucker lemma, all sets are
    full for some cell, and a count of the beads that have several possible owners shows that some
    choice is fair [fair_choice].

    In general, the pieces obtained for q1 thieves are put together to form q1 necklaces, which are
    split between q2 thieves [splits_prod]. *)

From mathcomp Require Import boot algebra.
From GC.GraphLib Require Import zp_tucker.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.

(** ** Barycentres in Z_p *)

Section Barycentre.
Variable p : nat.
Hypothesis p_prime : prime p.
Local Abbreviation F := 'Z_p.
Implicit Types (S : {set F}) (k x : F).
Local Open Scope ring_scope.

Lemma Zp_card : #|{: F}| = p.
Proof. by rewrite card_ord Zp_cast ?prime_gt1. Qed.

Lemma card_ltp S : S != setT -> (#|S| < p)%N.
Proof. by move=> ST; rewrite -[X in (_ < X)%N]Zp_card -cardsT proper_card // properT. Qed.

Lemma card_shift S k : #|[set x + k | x in S]| = #|S|.
Proof. exact/card_imset/addIr. Qed.

Definition bary S : F := (\sum_(x in S) x) / #|S|%:R.

Lemma bary_shift S k : S != set0 -> S != setT -> bary [set x + k | x in S] = bary S + k.
Proof.
move=> S0 ST; have u : #|S|%:R \is a @GRing.unit F.
  rewrite unitZpE ?prime_gt1 // prime_coprime // gtnNdvd ?card_gt0 ?card_ltp //.
rewrite /bary card_shift big_imset /=; first by move=> x y _ _; apply: addIr.
by rewrite big_split sumr_const /= -[k *+ _]mulr_natr mulrDl mulrK.
Qed.

End Barycentre.

(** ** A prime number of thieves *)

Section Prime.
Variables (p n : nat) (T : finType) (c : nat -> option T).
Hypotheses (p_prime : prime p) (n_gt0 : 0 < n).
Local Abbreviation F := 'Z_p.
Implicit Types (s : cell p) (k : T) (r : F) (a : {ffun 'I_n -> F}).

(** The thieves who can have the bead [b]. *)
Fixpoint owners s b : {set F} := if s is x :: s' then
    if b < x.1.2 then [set x.2] else if x.1.1 && (b == x.1.2) then x.2 |: owners s' b
    else owners s' b
  else set0.

Lemma owners_facet s f b : f \in facets s -> owners f.2 b \subset owners s b.
Proof.
elim: s f => // x s IH f.
apply: (facets_cons (P := fun s' => owners s' b \subset owners (x :: s) b)).
- case: x => [[[] k] r] //= _; case: (ltngtP b k) => [bk|kb|->] /=.
  + by rewrite ltnS (ltnW bk).
  + by rewrite ltnS leqNgt kb.
  + by rewrite ltnSn subsetUl.
- case: x => [[[] [|k]] r] //= _; first by case: eqP; rewrite ?subsetUr.
  by case: ifP => // _; case: eqP => // _; apply: subsetUr.
- move=> g /IH gs; rewrite /=; case: ifP => // _; case: ifP => // _; exact: setUS.
Qed.

Lemma owners_shc z s b : owners (shc z s) b = [set (x + z)%R | x in owners s b].
Proof.
elim: s => [|x s IH] /=; first by rewrite imset0.
by case: ifP; rewrite ?imset_set1 // IH; case: ifP; rewrite // imsetU imset_set1.
Qed.

Lemma owners_full s b : full n s -> b < n -> owners s b != set0.
Proof.
move=> + bn; elim: s => //= x s IH; rewrite /full /= => /orP[/andP[_ /eqP->]|/IH s0].
  by rewrite bn; apply/set0Pn; exists x.2; rewrite inE.
case: ifP => _; first by apply/set0Pn; exists x.2; rewrite inE.
by case: ifP => // _; apply/set0Pn; exists x.2; rewrite !inE eqxx.
Qed.

Lemma slack_le s : \sum_(b < n) #|owners s b|.-1 <= size s - full n s.
Proof.
elim: s => [|x s IH]; first by rewrite big1 // => b _; rewrite cards0.
rewrite /full /=; case: andP => [[/negbTE xv /eqP xn]|_] /=.
  by rewrite big1 // => b _; rewrite xn ltn_ord cards1.
apply: (@leq_trans (\sum_(b < n) ((x.1.2 == b :> nat) + #|owners s b|.-1))).
  apply: leq_sum => b _ /=; case: ifP => _; first by rewrite cards1.
  case: ifP => [/andP[_ bx]|_]; last exact: leq_addl.
  rewrite eq_sym bx cardsU1; case: (x.2 \in _) => /=; first by rewrite add0n leq_addl.
  by case: #|_|.
have fs : full n s <= size s by case: (s) => // y s'; apply: leq_trans (leq_b1 _) _.
rewrite big_split -/(full n s) subSn //= -[X in _ <= X]add1n leq_add //.
rewrite -(big_mkcond (fun b : 'I_n => x.1.2 == b) (fun=> 1)) sum1dep_card.
by apply/card_le1_eqP => b b'; rewrite !inE => /eqP xb /eqP xb'; apply/val_inj; rewrite /= -xb.
Qed.

(** Choices of an owner for each bead. *)
Definition choice s a := [forall b, a b \in owners s b].
(** Number of beads of type [k] of the thief [r]. *)
Definition share a k r := \sum_(b < n) ((c b == Some k) && (a b == r)).
Definition is_max a k r := [forall r', share a k r' <= share a k r].
(** [r] is the winner for the type [k]: the owner of the first bead of type [k] whose owner has
    the most beads of type [k]. *)
Definition wins a k r := [exists b : 'I_n, [&& c b == Some k, a b == r, is_max a k r &
  [forall b' : 'I_n, [&& b' < b, c b' == Some k & is_max a k (a b')] ==> false]]].
Definition winners s k := [set r | [exists a, choice s a && wins a k r]].
Definition used k := [exists b : 'I_n, c b == Some k].

Lemma winners_sub s s' k :
  (forall b, owners s b \subset owners s' b) -> winners s k \subset winners s' k.
Proof.
move=> ss'; apply/subsetP => r; rewrite !inE => /existsP[a /andP[/forallP ca wa]].
by apply/existsP; exists a; rewrite wa andbT; apply/forallP => b; apply: (subsetP (ss' b)).
Qed.

Lemma winners_shc x s k : winners (shc x s) k = [set (r + x)%R | r in winners s k].
Proof.
have sub y s' : [set (r + y)%R | r in winners s' k] \subset winners (shc y s') k.
  apply/subsetP => _ /imsetP[r + ->]; rewrite !inE => /existsP[a /andP[/forallP ca wa]].
  apply/existsP; exists [ffun b => (a b + y)%R]; apply/andP; split.
    by apply/forallP => b; rewrite ffunE owners_shc; apply/(imset_f (fun x => x + y)%R)/ca.
  have share_y r' : share [ffun b => (a b + y)%R] k (r' + y)%R = share a k r'.
    by apply: eq_bigr => b _; rewrite ffunE (inj_eq (addIr y)).
  have max_y r' : is_max [ffun b => (a b + y)%R] k (r' + y)%R = is_max a k r'.
    apply/forallP/forallP => h r2; first by rewrite -!share_y.
    by rewrite -[r2](subrK y) !share_y.
  case/existsP: wa => b /and4P[cb ab ta /forallP fb]; apply/existsP; exists b.
  rewrite cb ffunE (inj_eq (addIr y)) ab max_y ta /=; apply/forallP => b'.
  by rewrite ffunE max_y; apply: fb.
apply/eqP; rewrite eqEsubset sub andbT; apply/subsetP => r rW.
have := subsetP (sub (- x)%R (shc x s)) _ (imset_f _ rW).
have -> : shc (- x)%R (shc x s) = s.
  rewrite /shc -map_comp -[RHS]map_id; apply: eq_map => -[u z] /=; by rewrite addrK.
by move=> rW'; apply/imsetP; exists (r - x)%R => //; rewrite subrK.
Qed.

Lemma winners_neq0 s k : full n s -> used k -> winners s k != set0.
Proof.
move=> fs /existsP[b0 cb0]; have ob (b : 'I_n) := set0Pn _ (owners_full fs (ltn_ord b)).
pose a := [ffun b => xchoose (ob b)].
have ca : choice s a by apply/forallP => b; rewrite ffunE; apply: xchooseP.
case: (arg_maxnP (fun r => share a k r) (isT : xpredT (0%R : F))) => r0 _ r0max.
have : 0 < share a k r0.
  rewrite (leq_trans _ (r0max (a b0) isT)) // /share (bigD1 b0) //= cb0 eqxx.
  by [].
rewrite lt0n sum_nat_eq0 negb_forall => /existsP[b1]; rewrite eqb0 negbK => /andP[cb1 /eqP ab1].
pose P (b : 'I_n) := (c b == Some k) && is_max a k (a b).
have Pb1 : P b1 by rewrite /P cb1 ab1; apply/forallP => r; apply: r0max.
case: (arg_minnP (fun b : 'I_n => val b) Pb1) => b /andP[cb tb] bmin.
apply/set0Pn; exists (a b); rewrite inE; apply/existsP; exists a; rewrite ca.
apply/existsP; exists b; rewrite cb eqxx tb /=; apply/forallP => b'.
apply/implyP => /and3P[bb' cb' tb'].
by rewrite ltnNge bmin // /P cb' in bb'.
Qed.

(** The label of a cell. *)
Definition bad s k := used k && (winners s k != setT).
Definition label s : F := if [pick k | bad s k] is Some k then bary (winners s k) else 0%R.
Definition label_rk s := \sum_(k | used k) #|winners s k|.-1.

Lemma winners_setT z s k : (winners (shc z s) k == setT) = (winners s k == setT).
Proof.
rewrite winners_shc !eqEcard !subsetT /= (card_shift _ z); by [].
Qed.

Section Label.
Let M := #|[set k | used k]| * p.-1.
Hypothesis all_bad : forall s, inK n M s -> exists k, bad s k.

Lemma label_shc z s : inK n M s -> label (shc z s) = (label s + z)%R.
Proof.
move=> Ks; rewrite /label (eq_pick (_ : bad (shc z s) =1 bad s)) => [k|].
  by rewrite /bad winners_setT.
case: pickP => [k /andP[uk Wk]|no]; last by have [k] := all_bad Ks; rewrite no.
by rewrite winners_shc bary_shift // winners_neq0 //; case/andP: Ks.
Qed.

Lemma label_rk_lt s : inK n M s -> label_rk s < M.
Proof.
move=> Ks; have [k0 /andP[u0 W0]] := all_bad Ks; have /andP[fs _] := Ks.
rewrite /M -sum_nat_const (eq_bigl used) => [k|]; first by rewrite inE.
rewrite /label_rk !(bigD1 k0 u0) /= -addSn leq_add //; last first.
  by apply: leq_sum => k _; rewrite -!subn1 leq_sub2r // (leq_trans (max_card _)) ?Zp_card.
by rewrite ltn_predRL prednK ?card_gt0 ?winners_neq0 ?card_ltp.
Qed.

Lemma label_facet s f :
  inK n M s -> f \in facets s -> label f.2 = label s \/ label_rk f.2 < label_rk s.
Proof.
move=> Ks fs; have Wfs k : winners f.2 k \subset winners s k.
  by apply: winners_sub => b; apply: owners_facet.
have [/forall_inP e|] := boolP [forall (k | used k), winners f.2 k == winners s k].
  left; rewrite /label (eq_pick (_ : bad f.2 =1 bad s)) => [k|].
    by rewrite /bad; case uk: (used k) => //=; rewrite (eqP (e k uk)).
  by case: pickP => // k /andP[uk _]; rewrite (eqP (e k uk)).
rewrite negb_forall_in => /exists_inP[k0 u0 W0]; right; have /andP[full_s _] := Ks.
rewrite /label_rk !(bigD1 k0 u0) /= -addSn leq_add //; last first.
  by apply: leq_sum => k _; rewrite -!subn1 leq_sub2r // subset_leq_card.
rewrite ltn_predRL prednK ?card_gt0 ?winners_neq0 ?(full_facet full_s fs) //.
by apply: proper_card; rewrite properEneq W0 Wfs.
Qed.
End Label.

Lemma tucker_bad : ~ forall s, inK n (#|[set k | used k]| * p.-1) s -> exists k, bad s k.
Proof. by move=> h; apply: (zp_tucker n_gt0 (label_shc h) (label_rk_lt h) label_facet). Qed.

(** *** Fair choices *)

Section Fair.
Variables (s : cell p) (k : T) (C : nat).
Hypotheses (fs : full n s) (uk : used k) (Wk : winners s k = setT).
Hypothesis Ck : \sum_(b < n) (c b == Some k) = p * C.

Let may r := \sum_(b < n) ((c b == Some k) && (r \in owners s b)).
Let slack := \sum_(b < n | c b == Some k) #|owners s b|.-1.

Lemma sum_may : \sum_r may r = p * C + slack.
Proof.
rewrite -Ck exchange_big /slack [X in _ + X]big_mkcond -big_split /=; apply: eq_bigr => b _.
case: (c b == Some k) => /=; last by rewrite big1.
rewrite add1n prednK ?card_gt0 ?owners_full // -sum1_card [RHS]big_mkcond.
by apply: eq_bigr.
Qed.

Lemma sum_share a : \sum_r share a k r = p * C.
Proof.
rewrite -Ck exchange_big /=; apply: eq_bigr => b _.
rewrite (bigD1 (a b)) //= eqxx andbT big1 ?addn0 // => r /negbTE.
by rewrite eq_sym => ->; rewrite andbF.
Qed.

Lemma share_le a r : choice s a -> share a k r <= may r ?= iff
  [forall b : 'I_n, (c b == Some k) && (r \in owners s b) ==> (a b == r)].
Proof.
move=> /forallP ca; have le (b : 'I_n) : (c b == Some k) && (a b == r) <=
    (c b == Some k) && (r \in owners s b) ?= iff
    ((c b == Some k) && (r \in owners s b) ==> (a b == r)).
  have := ca b; case: (c b == Some k) => //=; case: eqP => [->->//|_ _].
  by case: (r \in _).
exact: (leqif_sum (fun (b : 'I_n) (_ : true) => le b)).
Qed.

Lemma winner r : exists a, [/\ choice s a, wins a k r & is_max a k r].
Proof.
have : r \in winners s k by rewrite Wk inE.
rewrite inE => /existsP[a /andP[ca wa]]; exists a; split=> //.
by case/existsP: wa => b /and4P[_ /eqP<-].
Qed.

Lemma is_max_ge a r : is_max a k r -> C <= share a k r.
Proof.
move=> /forallP ta; rewrite -(leq_pmul2l (prime_gt0 p_prime)) -(sum_share a).
rewrite -[X in X * share _ _ _](Zp_card p_prime) -sum_nat_const.
by apply: leq_sum => r' _.
Qed.

Lemma tight a r : choice s a -> is_max a k r -> may r = C -> forall r', share a k r' = C.
Proof.
move=> ca ta Mr; have [le _] := share_le r ca; rewrite Mr in le.
have le' r' : share a k r' <= C ?= iff (share a k r' == C).
  by split=> //; apply: leq_trans (forallP ta r') le.
have [_ /esym] := leqif_sum (fun r' (_ : true) => le' r').
rewrite sum_share sum_nat_const Zp_card // eqxx => /forallP all r'; exact/eqP/all.
Qed.

Lemma may_ge r : C <= may r.
Proof.
have [a [ca _ ta]] := winner r; apply: leq_trans (is_max_ge ta) _; exact: (share_le r ca).1.
Qed.

Lemma tight_uniq r r' : may r = C -> may r' = C -> r = r'.
Proof.
have first a (b b' : 'I_n) : (forall r, share a k r = C) ->
  [forall b' : 'I_n, [&& b' < b, c b' == Some k & is_max a k (a b')] ==> false] ->
  c b' == Some k -> b <= b'.
  move=> cC /forallP/(_ b') + cb'; rewrite cb' [b <= b']leqNgt; apply: contraL => -> /=.
  by rewrite implybF negbK; apply/forallP => r2; rewrite !cC.
move=> Mr Mr'; have [a [ca wa ta]] := winner r; have [a' [ca' wa' ta']] := winner r'.
have cC := tight ca ta Mr; have cC' := tight ca' ta' Mr'.
case/existsP: wa => b /and4P[cb /eqP ab _ fb]; case/existsP: wa' => b' /and4P[cb' /eqP ab' _ fb'].
have eb : b = b' by apply/val_inj/eqP; rewrite eqn_leq (first a b b') ?(first a' b' b).
have [_] := share_le r ca'; rewrite cC' Mr eqxx => /esym/forallP/(_ b).
by rewrite cb -{1}ab (forallP ca b) /= eb ab' => /eqP.
Qed.

Lemma slack_ge : p.-1 <= slack.
Proof.
have one : #|[set r | may r == C]| <= 1.
  by apply/card_le1_eqP => r r'; rewrite !inE => /eqP Mr /eqP/(tight_uniq Mr).
rewrite -(leq_add2l (p * C)) -sum_may.
have le : \sum_(r : F) (C + (may r != C)) <= \sum_r may r.
  apply: leq_sum => r _; case: eqP => [->|/eqP neq]; first by rewrite addn0.
  by rewrite addn1 ltn_neqAle eq_sym neq may_ge.
apply: leq_trans le; rewrite big_split sum_nat_const Zp_card //= leq_add2l.
rewrite -(big_mkcond (fun r => may r != C) (fun=> 1)) sum1dep_card -subn1 leq_subLR.
have := cardsC [set r | may r == C]; rewrite Zp_card // => {1}<-.
rewrite leq_add //; apply: eq_leq; apply: eq_card => r; by rewrite !inE.
Qed.

Lemma fair_choice : slack <= p.-1 -> exists2 a, choice s a & forall r, share a k r = C.
Proof.
move=> sl; have [/existsP[r /eqP Mr]|/existsPn no] := boolP [exists r, may r == C].
  by have [a [ca _ ta]] := winner r; exists a => //; apply: tight ta Mr.
have : \sum_(r : F) C.+1 <= \sum_r may r.
  by apply: leq_sum => r _; rewrite ltn_neqAle eq_sym no may_ge.
rewrite sum_nat_const Zp_card // sum_may mulnS addnC leq_add2l => /leq_trans/(_ sl).
by rewrite leqNgt ltn_predL prime_gt0.
Qed.

End Fair.

(** *** From choices to cuts *)

(** The owner of the bead [b] for a list of cuts. *)
Fixpoint owner (v : seq (nat * F)) b : F :=
  if v is x :: v' then if b < x.1 then x.2 else owner v' b else 0%R.

Lemma owner_cut v b : owner v b != owner v b.+1 -> b.+1 \in map fst v.
Proof.
elim: v => //= x v IH; rewrite inE; case: (ltngtP b.+1 x.1) => [bx|xb|->] //=.
  by rewrite eqxx.
Qed.

Lemma realize s (a : nat -> F) (B : pred nat) : (forall b, B b -> a b \in owners s b) ->
  exists v, [/\ size v = size s, full n s -> n \in map fst v & forall b, B b -> owner v b = a b].
Proof.
elim: s B => [|[[e k] r] s IH] B aB /=.
  by exists [::]; split=> // b /aB; rewrite inE.
pose k' := k + [&& e, B k & a k == r].
have [|v [sv fv ov]] := IH [pred b | B b & k' <= b].
  move=> b /andP[Bb]; have := aB b Bb; rewrite /= /k'.
  case: (ltngtP b k) => [bk _ /(leq_trans (leq_addr _ _))|kb|bk]; first by rewrite leqNgt bk.
    by rewrite andbF.
  move: Bb; rewrite bk => Bk; case: (e) => //=; rewrite Bk in_setU1 => /orP[->|//].
  by rewrite addn1 ltnn.
exists ((k', r) :: v); split=> [|/orP[/andP[/negbTE e0 /eqP kn]|fs]|b Bb] /=.
- by rewrite sv.
- by rewrite inE /k' e0 addn0 kn eqxx.
- by rewrite inE fv ?orbT.
case: (ltnP b k') => [bk'|k'b]; last by apply: ov; rewrite /= Bb.
have := aB b Bb; rewrite /=; case: (ltnP b k) => [_|kb]; first by rewrite inE => /eqP.
move: bk'; rewrite /k'; case: and3P => [[_ Bk /eqP <-]|_]; last by rewrite addn0 ltnNge kb.
by rewrite addn1 ltnS => bk; have -> : b = k by apply/eqP; rewrite eqn_leq bk.
Qed.

Lemma owner_cuts v : n \in map fst v -> \sum_(i < n.-1) (owner v i != owner v i.+1) < size v.
Proof.
move=> nv; pose cut i := owner v i != owner v i.+1.
rewrite -(big_mkord xpredT (fun i => nat_of_bool (cut i))) -(big_mkcond cut (fun=> 1)).
rewrite sum1_count /index_iota subn0.
rewrite -size_filter -(size_map succn) -(size_map fst v).
have sub : {subset [seq i.+1 | i <- iota 0 n.-1 & cut i] <= [seq k <- map fst v | k < n]}.
  move=> _ /mapP[i + ->]; rewrite !mem_filter mem_iota add0n => /andP[/owner_cut -> /=].
  by rewrite ltn_predRL andbT.
have u : uniq [seq i.+1 | i <- iota 0 n.-1 & cut i].
  by rewrite map_inj_uniq ?filter_uniq ?iota_uniq // => ? ? [].
apply: leq_ltn_trans (uniq_leq_size u sub) _.
rewrite size_filter -(count_predC (fun j => j < n) (map fst v)) -[X in X < _]addn0 ltn_add2l.
by rewrite -has_count; apply/hasP; exists n => //=; rewrite ltnn.
Qed.

(** *** Fair splitting *)

Hypothesis div : forall k, p %| \sum_(b < n) (c b == Some k).
Let C k := (\sum_(b < n) (c b == Some k)) %/ p.
Let M := #|[set k | used k]| * p.-1.

Lemma fair_vertex s : inK n M s -> (forall k, used k -> winners s k = setT) ->
  exists v, [/\ size v <= M.+1, n \in map fst v &
    forall k r, \sum_(b < n) ((c b == Some k) && (owner v b == r)) = C k].
Proof.
move=> /andP[fs sM] Ws; pose sl k := \sum_(b < n | c b == Some k) #|owners s b|.-1.
have Ck k : \sum_(b < n) (c b == Some k) = p * C k by rewrite mulnC divnK.
have sl_ge k : used k -> p.-1 <= sl k by move=> uk; apply: slack_ge (Ws k uk) (Ck k).
have sl_sum : \sum_(k | used k) sl k <= M.
  rewrite -ltnS (leq_trans _ sM) //; apply: leq_ltn_trans (_ : \sum_(b < n) #|owners s b|.-1 < _).
    rewrite (exchange_big_dep xpredT) //=; apply: leq_sum => b _.
    case cb: (c b) => [k0|]; last by rewrite big_pred0 // => k; rewrite andbF.
    rewrite (big_pred1 k0) // => k; rewrite /= (inj_eq Some_inj) eq_sym.
    case: eqP => [->|]; rewrite ?andbF ?andbT //; apply/existsP; exists b; exact/eqP.
  rewrite (leq_ltn_trans (slack_le s)) // fs subn1 ltn_predL.
  by case/hasP: fs => x; case: (s).
have sl_le k : used k -> sl k <= p.-1.
  move=> uk; rewrite -(leq_add2r (\sum_(k' | used k' && (k' != k)) p.-1)).
  rewrite -(bigD1 k) //= [X in _ <= X]sum_nat_cond_const (leq_trans _ sl_sum) //.
  by rewrite (bigD1 k uk) leq_add2l; apply: leq_sum => k' /andP[/sl_ge].
have ch k : exists a, used k -> choice s a /\ forall r, share a k r = C k.
  have [uk|_] := boolP (used k); last by exists [ffun=> 0%R].
  have [a ca aC] := fair_choice fs (Ws k uk) (Ck k) (sl_le k uk).
  by exists a.
have [a aP] := fin_all_exists ch.
have ob (b : 'I_n) := set0Pn _ (owners_full fs (ltn_ord b)).
pose a' (b : 'I_n) := if c b is Some k then a k b else xchoose (ob b).
have ca' b : a' b \in owners s b.
  rewrite /a'; case cb: (c b) => [k|]; last exact: xchooseP.
  by have [|/forallP] := aP k; first by apply/existsP; exists b; apply/eqP.
pose a1 i := if insub i is Some b then a' b else 0%R.
have [|v [sv fv ov]] := @realize s a1 (fun i => i < n).
  by move=> b bn; rewrite /a1 insubT; apply: ca'.
exists v; split=> [||k r]; [by rewrite sv | exact: fv|].
have [uk|nuk] := boolP (used k).
  have [_ /(_ r) <-] := aP k uk; apply: eq_bigr => b _; rewrite ov // /a1 valK /a'.
  by case: eqP => // ->.
have c0 (b : 'I_n) : (c b == Some k) = false by apply: contraNF nuk => cb; apply/existsP; exists b.
by rewrite /C !big1 ?div0n // => b _; rewrite c0.
Qed.

End Prime.

(** The theorem for a set [Q] of thieves; a bead may have no type. *)
Definition splits (Q : finType) := forall (T : finType) n (c : nat -> option T),
  (forall k, #|Q| %| \sum_(i < n) (c i == Some k)) -> exists a : nat -> Q,
  \sum_(i < n.-1) (a i != a i.+1) <= #|T| * #|Q|.-1 /\
  forall k j, \sum_(i < n) ((c i == Some k) && (a i == j)) = (\sum_(i < n) (c i == Some k)) %/ #|Q|.

Lemma splits_prime p : prime p -> splits 'Z_p.
Proof.
move=> p_prime T n c; rewrite Zp_card // => div.
have [->|n_gt0] := posnP n; first by exists (fun=> 0%R); split=> *; rewrite !big_ord0 ?div0n.
pose ok (a : {ffun 'I_n.+1 -> 'Z_p}) :=
  (\sum_(i < n.-1) (a (inord i) != a (inord i.+1)) <= #|T| * p.-1)
  && [forall k, forall j, \sum_(i < n) ((c i == Some k) && (a (inord i) == j))
                          == (\sum_(i < n) (c i == Some k)) %/ p].
have [/existsP[a /andP[cuts_a /forallP fair_a]]|/existsPn no] := boolP [exists a, ok a].
  by exists (a \o inord); split=> // k j; apply/eqP/(forallP (fair_a k)).
case: (@tucker_bad p n T c p_prime n_gt0) => s Ks; apply/existsP; apply: contraT => /existsPn nb.
have Ws k : used n c k -> winners n c s k = setT.
  by move=> uk; have := nb k; rewrite /bad uk negbK => /eqP.
have [v [sv nv fv]] := fair_vertex p_prime div Ks Ws.
have av i : i < n.+1 -> [ffun i : 'I_n.+1 => owner v i] (inord i) = owner v i.
  by move=> ni; rewrite ffunE inordK.
case/negP: (no [ffun i : 'I_n.+1 => owner v i]); apply/andP; split.
  rewrite (eq_bigr (fun i : 'I_n.-1 => nat_of_bool (owner v i != owner v i.+1))) => [i _|].
    have i1n : i.+1 < n by rewrite -ltn_predRL.
    by rewrite !av // ltnW // ltnW.
  rewrite -ltnS (leq_trans (owner_cuts nv)) // (leq_trans sv) // ltnS leq_mul2r.
  by rewrite max_card orbT.
apply/forallP => k; apply/forallP => j; rewrite -(fv k j); apply/eqP/eq_bigr => i _.
by rewrite av // leqW.
Qed.

(** ** Composition *)

Lemma splits_card (Q Q' : finType) : #|Q| = #|Q'| -> splits Q -> splits Q'.
Proof.
move=> e sQ T n c; rewrite -e => /sQ[a [cuts_a fair_a]].
pose f (x : Q) : Q' := enum_val (cast_ord e (enum_rank x)).
pose g (x : Q') : Q := enum_val (cast_ord (esym e) (enum_rank x)).
have fK : cancel f g by move=> x; rewrite /f /g enum_valK cast_ordK enum_rankK.
have gK : cancel g f by move=> x; rewrite /f /g enum_valK cast_ordKV enum_rankK.
exists (f \o a); split=> [|k j].
  by under eq_bigr => i _ do rewrite /= (can_eq fK).
by rewrite -(fair_a k (g j)); apply: eq_bigr => i _; rewrite /= (can2_eq fK gK).
Qed.

(** Number of elements of [P] before [i]. *)
Definition rnk (P : pred nat) i := count P (iota 0 i).

Lemma rnkS P i : rnk P i.+1 = rnk P i + P i.
Proof. by rewrite /rnk -[i.+1]addn1 iotaD count_cat /= addn0. Qed.

Lemma rnk_sum (P : pred nat) (g : nat -> nat) n :
  \sum_(i < n | P i) g (rnk P i) = \sum_(m < rnk P n) g m.
Proof.
elim: n => [|n IH]; first by rewrite !big_ord0.
rewrite rnkS big_mkcond big_ord_recr -big_mkcond /= IH.
by case: (P n); rewrite ?addn0 // addn1 big_ord_recr.
Qed.

Lemma nth_rnk (P : pred nat) n i : i < n -> P i -> nth 0 (filter P (iota 0 n)) (rnk P i) = i.
Proof.
move=> /subnKC <- Pi; rewrite addSnnS iotaD filter_cat nth_cat size_filter ltnn subnn /= add0n.
by rewrite Pi.
Qed.

Lemma rnk_path (P : pred nat) (g : nat -> nat) n :
  \sum_(i < n.-1 | P i && P i.+1) g (rnk P i) <= \sum_(m < (rnk P n).-1) g m.
Proof.
case: n => [|n]; first by rewrite big_ord0.
pose h m := if m is m'.+1 then g m' else 0.
have -> : \sum_(m < (rnk P n.+1).-1) g m = \sum_(m < rnk P n.+1) h m.
  by case: (rnk P n.+1) => [|N]; rewrite ?big_ord0 // [RHS]big_ord_recl.
rewrite -rnk_sum big_mkcond [X in _ <= X]big_mkcond big_ord_recl /= (leq_trans _ (leq_addl _ _)) //.
by apply: leq_sum => i _; rewrite /bump /= add1n rnkS; case: (P i) => //=; rewrite addn1.
Qed.

Lemma splits_prod (Q1 Q2 : finType) :
  0 < #|Q1| -> 0 < #|Q2| -> splits Q1 -> splits Q2 -> splits (Q1 * Q2)%type.
Proof.
move=> q1 q2 s1 s2 T n c; rewrite card_prod => div.
have div1 k : #|Q1| %| \sum_(i < n) (c i == Some k) by apply: dvdn_trans (dvdn_mulr _ _) (div k).
have [a1 [cuts1 fair1]] := s1 T n c div1.
pose P r i := a1 i == r; pose c' r m := c (nth 0 (filter (P r) (iota 0 n)) m).
have c'E r (g : option T -> nat -> nat) :
    \sum_(m < rnk (P r) n) g (c' r m) m = \sum_(i < n | P r i) g (c i) (rnk (P r) i).
  rewrite -(rnk_sum _ (fun m => g (c' r m) m)).
  by apply: eq_bigr => i Pi; rewrite /c' nth_rnk.
have c'k r k : \sum_(m < rnk (P r) n) (c' r m == Some k) = (\sum_(i < n) (c i == Some k)) %/ #|Q1|.
  rewrite (c'E r (fun x _ => x == Some k)) -(fair1 k r) big_mkcond /=.
  by apply: eq_bigr => i _; rewrite /P andbC; case: (a1 i == r).
have b_ex r : exists b : nat -> Q2,
    \sum_(m < (rnk (P r) n).-1) (b m != b m.+1) <= #|T| * #|Q2|.-1 /\
    forall k j, \sum_(m < rnk (P r) n) ((c' r m == Some k) && (b m == j))
      = (\sum_(i < n) (c i == Some k)) %/ #|Q1| %/ #|Q2|.
  have [k|b [cuts_b fair_b]] := s2 T (rnk (P r) n) (c' r).
    by rewrite c'k dvdn_divRL // mulnC div.
  by exists b; split=> // k j; rewrite fair_b c'k.
have [b bP] := fin_all_exists b_ex.
exists (fun i => (a1 i, b (a1 i) (rnk (P (a1 i)) i))); split=> [|k [r j]]; last first.
  have [_ /(_ k j)] := bP r; rewrite -divnMA => <-.
  rewrite (c'E r (fun x m => (x == Some k) && (b r m == j))).
  rewrite [RHS]big_mkcond /=; apply: eq_bigr => i _; rewrite /P xpair_eqE.
  by case: (a1 i =P r) => [->|]; rewrite ?andbF.
apply: (@leq_trans (\sum_(i < n.-1) (a1 i != a1 i.+1) +
  \sum_r \sum_(i < n.-1 | P r i && P r i.+1) (b r (rnk (P r) i) != b r (rnk (P r) i).+1))).
  rewrite (exchange_big_dep xpredT) //= -big_split; apply: leq_sum => i _ /=.
  rewrite xpair_eqE; case: (eqVneq (a1 i) (a1 i.+1)) => [e|_]; last exact: leq_trans (leq_b1 _) _.
  rewrite (big_pred1 (a1 i)) => [r|]; first by rewrite /P -e andbb eq_sym.
  by rewrite -e rnkS /P eqxx addn1.
apply: (@leq_trans (#|T| * #|Q1|.-1 + \sum_(r : Q1) #|T| * #|Q2|.-1)).
  rewrite leq_add //; apply: leq_sum => r _; apply: leq_trans (bP r).1.
  exact: (rnk_path (P r) (fun m => b r m != b r m.+1)).
rewrite sum_nat_const mulnCA -mulnDr leq_mul2l -[#|xpredT|]/#|Q1|; apply/orP; right.
by move: q1 q2; case: #|Q1| => // x _; case: #|Q2| => // y _; rewrite mulnS.
Qed.

Lemma splits_ord q : 0 < q -> splits 'I_q.
Proof.
elim/ltn_ind: q => q IH q_gt0; have [q1|q1] := leqP q 1.
  apply: (@splits_card unit); first by rewrite card_unit card_ord; case: (q) q_gt0 q1 => [|[]].
  move=> T n c _; exists (fun=> tt); split=> [|k []]; rewrite card_unit ?divn1.
    by rewrite big1.
  by apply: eq_bigr => i _; rewrite eqxx andbT.
have p_prime := pdiv_prime q1; have pq := pdiv_dvd q.
have q'_gt0 : 0 < q %/ pdiv q by rewrite divn_gt0 ?pdiv_gt0 // dvdn_leq.
apply: (@splits_card ('Z_(pdiv q) * 'I_(q %/ pdiv q))%type).
  by rewrite card_prod Zp_card // !card_ord mulnC divnK.
apply: splits_prod; rewrite ?Zp_card ?card_ord ?pdiv_gt0 //; first exact: splits_prime.
by apply: IH; rewrite ?ltn_Pdiv ?prime_gt1.
Qed.

Theorem splitting_necklace_theorem (n t q : nat) (c : 'I_n -> 'I_t) :
  0 < q -> (forall k : 'I_t, q %| #|[set i | c i == k]|) ->
  exists a : 'I_n -> 'I_q,
    #|[set pr : 'I_n * 'I_n | (pr.2 == pr.1.+1 :> nat) && (a pr.1 != a pr.2)]| <= t * q.-1
    /\ forall (k : 'I_t) (j : 'I_q),
         #|[set i | (c i == k) && (a i == j)]| = #|[set i | c i == k]| %/ q.
Proof.
move=> q_gt0 div; pose c' i := omap c (insub i).
have card_sum (P : pred 'I_n) (P' : nat -> bool) : (forall i : 'I_n, P' i = P i) ->
    #|[set i | P i]| = \sum_(i < n) P' i.
  by move=> e; rewrite -sum1dep_card big_mkcond; apply: eq_bigr => i _; rewrite e.
have c'E k (i : 'I_n) : (c' i == Some k) = (c i == k) by rewrite /c' valK.
have cardk k : #|[set i | c i == k]| = \sum_(i < n) (c' i == Some k).
  exact: (card_sum _ (fun i => c' i == Some k) (c'E k)).
have [k|a [cuts_a fair_a]] := splits_ord q_gt0 (n := n) (c := c').
  by rewrite card_ord -cardk.
rewrite !card_ord in cuts_a fair_a; exists (fun i => a i); split=> [|k j]; last first.
  rewrite (card_sum _ (fun i => (c' i == Some k) && (a i == j))) => [i|]; first by rewrite c'E.
  by rewrite fair_a cardk.
apply: leq_trans cuts_a; case: n {c div c' card_sum c'E cardk fair_a} => [|n].
  by rewrite (eq_card0 (A := _)) // => -[[]].
pose f (i : 'I_n) := (widen_ord (leqnSn n) i, lift ord0 i).
apply: (@leq_trans #|f @: [set i | a (val (f i).1) != a (val (f i).2)]|).
  apply/subset_leq_card/subsetP => -[i j]; rewrite !inE /= => /andP[/eqP ji aij].
  have i_lt : i < n by rewrite -ltnS -ji ltn_ord.
  have fi : f (Ordinal i_lt) = (i, j) by congr (_, _); apply: val_inj; rewrite //= ji.
  by rewrite -fi imset_f // inE /= /bump add1n -ji.
apply: leq_trans (leq_imset_card _ _) _; rewrite -sum1dep_card big_mkcond.
by apply: leq_sum => i _ /=; rewrite /bump add1n.
Qed.
