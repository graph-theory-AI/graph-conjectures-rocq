(** * Random matchings of squares

We construct, by a nibble with R rounds, a random matching of squares of Q_(Rn+m) such that each
vertex is uncovered with probability at most 1/(2K), where R = 256 K^4, and each outcome [Q] has
probability at most P^(-|Q|), where P = 8 C(n,2).

One round passes from Q_m to Q_(n+m) = Q_n x Q_m.  Take independent random matchings of the
copies of Q_m.  Select each square S x {x}, where S is a square of Q_n, independently with
probability 1/P, and add those that meet no other selected square and no square of the matchings
of the copies of Q_m.  As S meets at most P/2 squares, it is selected with no conflict with
probability at least 1/(2P).  If x is uncovered with probability t in Q_m, then the 4 vertices of
S x {x} are in different copies of Q_m, hence they are all uncovered with probability t^4.
Each vertex (a,x) is in P/8 squares S x {x}, so it is uncovered after the round with probability
at most t - t^4/16, which is at most t - 1/R when t > 1/(2K). *)

From GraphTheory Require Import digraph sgraph.
From GC.packing.AX_hypercube_subcube_partitions_dimension_2_asymptotics
  Require Import squares gluing.
From mathcomp Require Import boot zify_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Counting *)

Lemma card_ffun_forall (T X : finType) (A : {set T}) (F : T -> pred X) :
  #|[set f : {ffun T -> X} | [forall t in A, F t (f t)]]| * #|X| ^ #|A|
    = \prod_(t in A) #|F t| * #|{ffun T -> X}|.
Proof.
have -> : #|[set f : {ffun T -> X} | [forall t in A, F t (f t)]]|
    = #|family (fun t => if t \in A then F t else predT)|.
  apply: eq_card => f; rewrite inE; apply/forall_inP/familyP => h t.
    by case: ifP => // tA; apply: h.
  by move=> tA; have := h t; rewrite tA.
rewrite card_family foldrE big_map big_enum /= card_ffun -(cardsC A) expnD mulnCA [RHS]mulnC.
congr (_ * _); rewrite (bigID (mem A)) /=; congr (_ * _); first by apply: eq_bigr => t ->.
by rewrite -prod_nat_const; apply: eq_big => [t|t /negPf->] //; rewrite inE.
Qed.

Lemma leq_card_bigcup (I T : finType) (D : {pred I}) (F : I -> {set T}) :
  #|\bigcup_(i in D) F i| <= \sum_(i in D) #|F i|.
Proof.
elim/big_rec2: _ => [|i s B _ leB]; first by rewrite cards0.
by rewrite (leq_trans (leq_card_setU _ _)) // leq_add2l.
Qed.

(** If the sets of [K w] are pairwise disjoint for each [w], then the numbers of [w] such that
    [S] is in [K w], for the sets [S] containing [a], add up to at most the number of [w] such
    that [K w] covers [a]. *)
Lemma sum_card_mem_cover (T W : finType) (K : W -> {set {set T}}) (E : {set {set T}}) (a : T) :
  (forall w, trivIset (K w)) ->
  \sum_(S in E | a \in S) #|[set w | S \in K w]| <= #|[set w | a \in cover (K w)]|.
Proof.
move=> triv; rewrite -[leqRHS]sum1_card.
rewrite (partition_big (fun w => pblock (K w) a) predT) //=.
rewrite [leqRHS](bigID (fun S => (S \in E) && (a \in S))) /= -[leqLHS]addn0 leq_add //.
apply: leq_sum => S /andP[_ aS]; rewrite sum1dep_card subset_leq_card //.
apply/subsetP => w; rewrite !inE => SK; rewrite (def_pblock (triv w) SK aS) eqxx andbT.
by apply/bigcupP; exists S.
Qed.

(** ** One round *)

Section Round.
Variables (n m p : nat) (Om : finType) (M : Om -> {set {set hypercube m}}).
Hypothesis PE : p.+1 = 8 * 'C(n, 2).
Hypothesis matM : forall w, M w \in matchings m.
Implicit Types (S : {set hypercube n}) (a z : hypercube n) (x : hypercube m).

(** A coin with P = p+1 faces for each square S x {x}, which is selected if the coin is 0. *)
Abbreviation coins := {ffun {set hypercube n} * hypercube m -> 'I_p.+1}.
Abbreviation round := ({ffun hypercube n -> Om} * coins)%type.

(** The selected squares without conflict of the column of [x]. *)
Definition selected (c : coins) x : {set {set hypercube n}} :=
  [set S in squares n | (c (S, x) == ord0) &&
     [forall S' in squares n, (S' != S) && (S' :&: S != set0) ==> (c (S', x) != ord0)]].

(** Those whose vertices are uncovered in the copies of Q_m. *)
Definition kept (w : round) x : {set {set hypercube n}} :=
  [set S in selected w.2 x | [forall z in S, x \notin cover (M (w.1 z))]].

Definition round_matching (w : round) : {set {set hypercube (n + m)}} :=
  glue (fun z => M (w.1 z)) (kept w).

Lemma kept_matching w x : kept w x \in matchings n.
Proof.
apply/matchingP; split; first by apply/subsetP => S /[!inE] /andP[/andP[]].
apply/trivIsetP => S S' /[!inE] /andP[/and3P[Ssq /eqP S0 _] _] /andP[/and3P[_ _ /forall_inP h] _].
by move=> SS'; have := h S; rewrite inE Ssq SS' S0 eqxx implybF negbK setI_eq0; apply.
Qed.

Lemma kept_disjoint w x S z : S \in kept w x -> z \in S -> x \notin cover (M (w.1 z)).
Proof. by rewrite inE => /andP[_ /forall_inP]; apply. Qed.

Lemma round_matchingP w : round_matching w \in matchings (n + m).
Proof.
apply: glue_matching => [z|x|x S z]; by [|apply: kept_matching|apply: kept_disjoint].
Qed.

(** The outcomes of the coins such that those of [A] are 0: they have probability P^(-|A|). *)
Definition coins0 (A : {set {set hypercube n} * hypercube m}) : {set coins} :=
  [set c : coins | [forall t in A, c t == ord0]].

Lemma card_coins0 A : #|coins0 A| * p.+1 ^ #|A| = #|{: coins}|.
Proof.
have := @card_ffun_forall _ 'I_p.+1 A (fun=> pred1 ord0).
by rewrite card_ord prod_nat_const card1 exp1n mul1n.
Qed.

(** A square is selected without conflict with probability at least 1/(2P), as it meets at most
    P/2 other squares. *)
Lemma card_selected S x : S \in squares n ->
  #|{: coins}| <= 2 * p.+1 * #|[set c : coins | S \in selected c x]|.
Proof.
move=> Ssq; pose E := [set S' in squares n | S' :&: S != set0] :\ S.
pose D := \bigcup_(S' in E) coins0 [set (S, x); (S', x)].
have cardE : #|E| <= 4 * 'C(n, 2).
  by apply: leq_trans (card_squares_meet Ssq); rewrite subset_leq_card ?subD1set.
have subD : coins0 [set (S, x)] \subset [set c : coins | S \in selected c x] :|: D.
  apply/subsetP => c; rewrite !inE => /forall_inP/(_ _ (set11 _)) c0.
  have [|nD] := boolP (c \in D); rewrite ?orbT // orbF c0; rewrite inE in Ssq; rewrite Ssq /=.
  apply/forall_inP => S' /[!inE] S'sq; apply/implyP => /andP[S'S S'I].
  apply: contra nD => c'0; apply/bigcupP; exists S'; rewrite !inE ?S'S ?S'sq //.
  by apply/forall_inP => t; rewrite !inE => /orP[]/eqP->.
have cardD : #|D| * p.+1 ^ 2 <= #|E| * #|{: coins}|.
  rewrite (leq_trans (leq_mul (leq_card_bigcup _ _) (leqnn _))) // big_distrl -sum_nat_const.
  apply: leq_sum => S'; rewrite inE => /andP[S'S _].
  rewrite -(card_coins0 [set (S, x); (S', x)]) cards2 xpair_eqE eqxx andbT eq_sym.
  by rewrite inE in S'S; rewrite S'S.
have := card_coins0 [set (S, x)]; rewrite cards1 expn1 => card0.
have := leq_mul (leq_trans (subset_leq_card subD) (leq_card_setU _ _)) (leqnn p.+1).
have leD : 2 * (#|D| * p.+1) <= #|{: coins}|.
  rewrite -(@leq_pmul2r p.+1) // -!mulnA mulnn; apply: leq_trans (leq_mul (leqnn 2) cardD) _.
  by rewrite mulnA [leqRHS]mulnC leq_mul //; lia.
by rewrite mulnDl card0; move: leD; move: #|D| #|{: coins}| #|[set c : coins | _]| => d C e; lia.
Qed.

(** The outcomes such that [x] is uncovered in all the copies [z] of Q_m, for [z] in [A]. *)
Definition uncovered x (A : {set hypercube n}) : {set {ffun hypercube n -> Om}} :=
  [set f : {ffun hypercube n -> Om} | [forall z in A, x \notin cover (M (f z))]].

Lemma card_uncovered x A :
  #|uncovered x A| * #|Om| ^ #|A|
    = #|[set w | x \notin cover (M w)]| ^ #|A| * #|{: {ffun hypercube n -> Om}}|.
Proof.
rewrite (@card_ffun_forall _ Om A (fun=> [pred w | x \notin cover (M w)])) prod_nat_const.
by rewrite cardsE.
Qed.

(** If [t] and [t'] are the probabilities that [x] and (a,x) are uncovered before and after the
    round, then t' <= t - t^4/16. *)
Lemma round_uncovered (v : hypercube (n + m)) :
  16 * (#|[set w | v \notin cover (round_matching w)]| * #|Om| ^ 4)
      + #|[set w | bot v \notin cover (M w)]| ^ 4 * #|{: round}|
    <= 16 * (#|[set w | bot v \notin cover (M w)]| * #|Om| ^ 3 * #|{: round}|).
Proof.
set u' := #|[set w | v \notin _]|; set u := #|[set w | bot v \notin _]|.
pose x := bot v; pose a := top v.
pose cov := [set w : round | a \in cover (kept w x)].
have covE : u' + #|cov| = #|uncovered x [set a]| * #|{: coins}|.
  rewrite -[#|{: coins}|]cardsT -cardsX -[RHS](cardsID cov) [RHS]addnC; congr (_ + _).
    apply: eq_card => w; rewrite !inE andbT cover_glue negb_or andbC; congr (_ && _).
    by apply/idP/forall_inP => [h z /set1P->|/(_ a (set11 a))].
  apply: eq_card => w; rewrite !inE andbT andb_idl // => /bigcupP[S SK aS].
  by apply/forall_inP => z /set1P->; apply: kept_disjoint SK aS.
have le_cov : u ^ 4 * #|{: round}| <= 16 * (#|cov| * #|Om| ^ 4).
  have k0 : 0 < 'C(n, 2) by lia.
  rewrite -(leq_pmul2l k0) -{1}(degree_squares a) -sum_nat_const.
  have : 2 * p.+1 * #|Om| ^ 4 * (\sum_(S in squares n | a \in S) #|[set w | S \in kept w x]|)
      <= 'C(n, 2) * (16 * (#|cov| * #|Om| ^ 4)).
    have -> : 'C(n, 2) * (16 * (#|cov| * #|Om| ^ 4)) = 2 * p.+1 * #|Om| ^ 4 * #|cov| by lia.
    rewrite leq_mul2l sum_card_mem_cover ?orbT // => w.
    by have [] := matchingP (kept_matching w x).
  apply: leq_trans; rewrite big_distrr /=.
  under eq_bigl do rewrite inE; apply: leq_sum => S /andP[Ssq _].
  (* the coins and the matchings of the copies of Q_m are independent *)
  have -> : #|[set w | S \in kept w x]|
      = #|uncovered x S| * #|[set c : coins | S \in selected c x]|.
    by rewrite -cardsX; apply: eq_card => w; rewrite !inE andbC.
  have unc : #|uncovered x S| * #|Om| ^ 4 = u ^ 4 * #|{: {ffun hypercube n -> Om}}|.
    by rewrite -(card_square Ssq) card_uncovered.
  rewrite card_prod [leqLHS]mulnA; apply: leq_trans (leq_mul (leqnn _) (card_selected x Ssq)) _.
  by rewrite -unc; move: #|_| (#|_| ^ 4) #|_| => A Z B; lia.
have unc : #|uncovered x [set a]| * #|Om| = u * #|{: {ffun hypercube n -> Om}}|.
  by have := card_uncovered x [set a]; rewrite cards1 !expn1.
have -> : u * #|Om| ^ 3 * #|{: round}| = (u' + #|cov|) * #|Om| ^ 4.
  by rewrite covE card_prod (expnS _ 3) [RHS]mulnACA unc mulnACA [#|{: coins}| * _]mulnC.
lia.
Qed.

(** The probability of each outcome [Q] of the round is at most P^(-|Q|), if this holds for the
    given random matchings of Q_m. *)
Lemma round_outcome (Q : {set {set hypercube (n + m)}}) :
  (forall Q', #|[set w | M w == Q']| * p.+1 ^ #|Q'| <= #|Om|) ->
  #|[set w | round_matching w == Q]| * p.+1 ^ #|Q| <= #|{: round}|.
Proof.
move=> outM; have [->|[w0]] := set_0Vmem [set w | round_matching w == Q]; first by rewrite cards0.
rewrite inE => /eqP eqQ.
(* the matchings of the copies of Q_m and the kept squares are determined by Q *)
pose row z := [set C in squares m | rect [set z] C \in Q].
pose col x := [set S in squares n | rect S [set x] \in Q].
pose B := [set t | t.1 \in col t.2].
have rowE (w : round) : round_matching w = Q -> forall z, M (w.1 z) = row z.
  by move=> wQ z; rewrite /row -wQ; apply: (glue_row (N := fun z => M (w.1 z))).
have colE (w : round) : round_matching w = Q -> forall x, kept w x = col x.
  by move=> wQ x; rewrite /col -wQ; apply: glue_column => x'; apply: kept_matching.
have leQ : #|Q| <= \sum_z #|row z| + #|B|.
  rewrite -{1}eqQ (leq_trans (card_glue _ _)) // leq_add //.
    by apply: leq_sum => z _; rewrite (rowE w0).
  by apply/subset_leq_card/subsetP => t; rewrite [t \in _]in_set [t \in B]in_set (colE w0).
pose F := [set f : {ffun hypercube n -> Om} | [forall z in setT, M (f z) == row z]].
have sub : [set w | round_matching w == Q] \subset setX F (coins0 B).
  apply/subsetP => -[f c]; rewrite inE => /eqP wQ; rewrite in_setX; apply/andP; split; rewrite inE.
    by apply/forall_inP => z _; rewrite (rowE _ wQ).
  apply/forall_inP => -[S x]; rewrite [_ \in B]in_set -(colE _ wQ) !inE.
  by case/andP => /and3P[].
have leF : #|F| * p.+1 ^ (\sum_z #|row z|) <= #|{: {ffun hypercube n -> Om}}|.
  have Om0 : 0 < #|Om| ^ #|[set: hypercube n]|.
    by rewrite expn_gt0; apply/orP; left; apply/card_gt0P; exists (w0.1 [tuple of nseq n false]).
  rewrite -(leq_pmul2r Om0) mulnAC (@card_ffun_forall _ Om setT (fun z => [pred w | M w == row z])).
  rewrite mulnAC mulnC leq_mul2l; apply/orP; right.
  rewrite -prod_nat_const expn_sum !(eq_bigl _ _ (@in_setT _)) -big_split.
  by apply: leq_prod => z _; have := outM (row z); rewrite cardsE.
have leX := subset_leq_card sub; rewrite cardsX in leX.
apply: leq_trans (leq_mul leX (leq_pexp2l (ltn0Sn p) leQ)) _.
by rewrite expnD mulnACA card_coins0 card_prod leq_mul.
Qed.

End Round.

(** If t' <= t - t^4/16, where t = u/Z and t' = u'/Z', then t' <= t, and t' <= t - 1/R when
    t > 1/(2K). *)
Lemma round_arith (K R r u u' Z Z' : nat) : 0 < Z -> R = 256 * K ^ 4 ->
  16 * (u' * Z ^ 4) + u ^ 4 * Z' <= 16 * (u * Z ^ 3 * Z') ->
  2 * K * u <= Z \/ R * u + r * Z <= R * Z ->
  2 * K * u' <= Z' \/ R * u' + r.+1 * Z' <= R * Z'.
Proof.
move=> Z0 RE step IH.
have Z3 : 0 < Z ^ 3 by rewrite expn_gt0 Z0.
have decr : u' * Z <= u * Z'.
  by rewrite -(leq_pmul2r Z3) -mulnA -expnS mulnAC; lia.
case: (leqP (2 * K * u) Z) IH => [small _|large [|IH]]; last 1 first.
- right; rewrite -(leq_pmul2r Z0).
  have : R * (u' * Z) + Z * Z' <= R * (u * Z').
    have large4 : Z ^ 4 * Z' <= (2 * K * u) ^ 4 * Z' by rewrite leq_mul2r leq_exp2r // ltnW // orbT.
    rewrite -(leq_pmul2r Z3); move: large4 step; rewrite RE !expnS !expn0; nia.
  by move: (leq_mul IH (leqnn Z')); lia.
- left; rewrite -(leq_pmul2r Z0).
  rewrite -mulnA (leq_trans (leq_mul (leqnn _) decr)) // mulnA [leqRHS]mulnC.
  by rewrite leq_mul2r small orbT.
- by [].
Qed.

(** ** Iteration *)

(** After [r] rounds: each outcome [Q] has probability at most P^(-|Q|), and the probability that
    a vertex is uncovered is at most 1/(2K) or 1 - r/R. *)
Definition random_matching (K R P r m : nat) : Prop :=
  exists (Om : finType) (M : Om -> {set {set hypercube m}}),
  [/\ 0 < #|Om|, forall w, M w \in matchings m,
      forall Q, #|[set w | M w == Q]| * P ^ #|Q| <= #|Om|
    & forall x, let u := #|[set w | x \notin cover (M w)]| in
        2 * K * u <= #|Om| \/ R * u + r * #|Om| <= R * #|Om|].

Lemma random_matching0 K R P m : random_matching K R P 0 m.
Proof.
exists unit, (fun=> set0); split=> [|w|Q|x /=].
- by rewrite card_unit.
- by rewrite inE sub0set /trivIset /cover !big_set0 cards0.
- have [<-|Q0] := eqVneq set0 Q; first by rewrite cards0 muln1 max_card.
  rewrite (_ : [set _ | _] = set0) ?cards0 //; apply/setP => w; rewrite !inE; exact/negPf.
- by right; rewrite mul0n addn0 leq_mul2l max_card orbT.
Qed.

Lemma random_matchingS K n r m : 1 < n ->
  random_matching K (256 * K ^ 4) (8 * 'C(n, 2)) r m ->
  random_matching K (256 * K ^ 4) (8 * 'C(n, 2)) r.+1 (n + m).
Proof.
move=> n1 [Om [M [Om0 matM outM uncM]]].
have [p PE] : exists p, p.+1 = 8 * 'C(n, 2).
  by exists (8 * 'C(n, 2)).-1; rewrite prednK // muln_gt0 bin_gt0.
rewrite -PE in outM *; exists ({ffun hypercube n -> Om} * _)%type, (@round_matching n m p Om M).
split=> [|w|Q|v u].
- by rewrite card_prod !card_ffun muln_gt0 !expn_gt0 Om0 card_ord.
- exact: round_matchingP.
- exact: round_outcome.
- by have := round_arith Om0 erefl (round_uncovered M PE v) (uncM (bot v)).
Qed.

Lemma random_matchingP K n r m : 1 < n ->
  random_matching K (256 * K ^ 4) (8 * 'C(n, 2)) r (r * n + m).
Proof.
move=> n1; elim: r => [|r IH]; first exact: random_matching0.
by rewrite mulSn -addnA; apply: random_matchingS.
Qed.

(** ** The number of matchings *)

Theorem many_matchings K n m d : 0 < K -> 1 < n -> d = 256 * K ^ 4 * n + m ->
  (8 * 'C(n, 2)) ^ (K.-1 * 2 ^ d) <= (2 * #|matchings d|) ^ (4 * K).
Proof.
move=> K0 n1 dE; set P := 8 * _; have P0 : 0 < P by rewrite muln_gt0 bin_gt0.
pose R := 256 * K ^ 4; have R0 : 0 < R by rewrite muln_gt0 expn_gt0 K0.
have [Om [M [Z0 matM outM uncM]]] : random_matching K R P R d.
  by rewrite dE; apply: random_matchingP.
have unc x : 2 * K * #|[set w | x \notin cover (M w)]| <= #|Om|.
  case: (uncM x) => // le; suff -> : #|[set w | x \notin cover (M w)]| = 0 by rewrite muln0.
  by move: le; rewrite -[leqRHS]add0n leq_add2r leqn0 muln_eq0 eqn0Ngt R0 => /eqP.
pose U w := #|~: cover (M w)|.
have sumU : 2 * K * (\sum_w U w) <= 2 ^ d * #|Om|.
  have -> : \sum_w U w = \sum_(x : hypercube d) #|[set w | x \notin cover (M w)]|.
    under eq_bigr do rewrite /U -sum1_card big_mkcond; rewrite exchange_big.
    apply: eq_bigr => x _; rewrite -sum1dep_card [RHS]big_mkcond; apply: eq_bigr => w _.
    by rewrite inE.
  by rewrite big_distrr -card_hypercube -sum_nat_const leq_sum.
pose G := [set w | K * U w <= 2 ^ d].
have halfG : #|Om| <= 2 * #|G|.
  have : #|~: G| * 2 ^ d <= K * \sum_w U w.
    rewrite big_distrr -sum_nat_const [leqRHS](bigID (mem (~: G))) /= -[leqLHS]addn0 leq_add //.
    by apply: leq_sum => w; rewrite !inE -ltnNge => /ltnW.
  have := cardsC G; have : 0 < 2 ^ d by rewrite expn_gt0.
  move: sumU; move: (2 ^ d) => D; nia.
have [w0 w0G] : exists w, w \in G by apply/card_gt0P; lia.
have [w wG minw] := @arg_minnP _ w0 (fun w => w \in G) (fun w => #|M w|) w0G; pose s := #|M w|.
have Ps : P ^ s <= 2 * #|matchings d|.
  rewrite -(leq_pmul2r Z0); apply: (leq_trans (leq_mul (leqnn _) halfG)).
  rewrite mulnCA -mulnA leq_mul2l /= -sum_nat_const mulnC.
  rewrite -[#|G|]sum1_card (partition_big M (mem (matchings d))) //= big_distrl.
  apply: leq_sum => Q _; rewrite sum1dep_card; apply: leq_trans (outM Q).
  have [->|[w' /setIdP[w'G /eqP eqQ]]] := set_0Vmem [set w' in G | M w' == Q].
    by rewrite cards0.
  rewrite leq_mul ?leq_pexp2l // -?eqQ ?minw //.
  by apply/subset_leq_card/subsetP => w''; rewrite !inE => /andP[].
have le_s : K.-1 * 2 ^ d <= s * (4 * K).
  have := cardsC (cover (M w)); rewrite card_hypercube (card_matching (matM w)) -/s -/(U w).
  by move: wG; rewrite inE -subn1 mulnBl mul1n; nia.
by rewrite (leq_trans (leq_pexp2l P0 le_s)) // expnM leq_exp2r // muln_gt0.
Qed.
