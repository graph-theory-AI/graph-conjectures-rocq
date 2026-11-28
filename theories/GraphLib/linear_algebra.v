(** * Linear algebra over the rationals: generic coefficients and ranks

Pattern matrices and independent rows, as used in rank arguments of combinatorics.

A pattern matrix is a square matrix whose entries are 0 or variables (an entry [Some s] of the
pattern is the variable [s], an entry [None] is 0), evaluated at an assignment [x] of the
variables.  Finitely many pattern minors that are each nonzero at some assignment are nonzero
together at a common assignment [common_nonvanishing].  The proof restricts the determinants
to a line instead of using multivariate polynomials: if [x] makes the first minors nonzero and
[y] makes a new one nonzero, the determinants along [x + t (y - x)] are univariate polynomials
in [t], all nonzero (at [t = 0] or at [t = 1]), and their product has a non-root among the
integers [0, ..., d].

The independence of a set of rows is stated directly on row vectors ([free_rows]): a
combination of these rows vanishes only trivially.  A nonzero minor makes its rows independent,
the rows of a matrix split into blocks with disjoint column supports are independent when each
block is, and the rank is at most the size of a cover of the nonzero entries by rows and
columns.

Used by the proof of Seymour's second neighbourhood conjecture
(theories/digraph/OPG_seymour_second_neighborhood_outdegree), which follows the paper of
OpenAI, a model-generated manuscript that is not peer reviewed,
https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/preprints/A-proof-of-Seymours-second-neighborhood-conjecture-September-23-2026/paper.pdf
and its Lean formalization (GenericRank.lean, GenericRankSupport.lean),
https://github.com/openai/math/tree/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Combinatorics/SecondNeighborhood *)

From mathcomp Require Import boot order algebra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** ** Indexing a set by ordinals *)

(** The [i]-th element of [S] (in the enumeration order of its type). *)
Definition idx (T : finType) (S : {set T}) (i : 'I_#|S|) : T := enum_val i.

Lemma idxP (T : finType) (S : {set T}) (i : 'I_#|S|) : idx i \in S.
Proof. exact: enum_valP. Qed.

Lemma idx_inj (T : finType) (S : {set T}) : injective (@idx T S).
Proof. exact: enum_val_inj. Qed.

Lemma idx_onto (T : finType) (S : {set T}) (x : T) : x \in S -> exists i : 'I_#|S|, idx i = x.
Proof. by move=> xS; exists (enum_rank_in xS x); exact: enum_rankK_in. Qed.

(** The indices of the images in [S] of the members of [A] by a map injective on [A]. *)
Lemma card_idx_imset (T T' : finType) (S : {set T}) (A : {set T'}) (f : T' -> T) :
  {in A &, injective f} -> {in A, forall e, f e \in S} ->
  #|[set i : 'I_#|S| | idx i \in f @: A]| = #|A|.
Proof.
move=> fI fS; rewrite -(card_in_imset fI) -(card_imset _ (@idx_inj _ S)); apply: eq_card => x.
apply/imsetP/idP => [[i]|xA]; first by rewrite inE => iA ->.
by case/imsetP: (xA) => e /fS + xe; rewrite -xe => /idx_onto[i ix]; exists i; rewrite ?inE ix.
Qed.

(** ** Pattern matrices and a common nonvanishing assignment *)

Section Patterns.
Variable sigma : Type.

Definition pattern_mx n (pat : 'I_n -> 'I_n -> option sigma) (x : sigma -> rat) : 'M[rat]_n :=
  \matrix_(i, j) oapp x 0 (pat i j).

Lemma eq_pattern_mx n (pat : 'I_n -> 'I_n -> option sigma) (x y : sigma -> rat) :
  x =1 y -> pattern_mx pat x = pattern_mx pat y.
Proof. by move=> xy; apply/matrixP => i j; rewrite !mxE; case: (pat i j) => //= s. Qed.

(** The determinant of a pattern along the line [x + t (y - x)], as a polynomial in [t]. *)
Definition line_det (x y : sigma -> rat) n (pat : 'I_n -> 'I_n -> option sigma) : {poly rat} :=
  \det (\matrix_(i, j) oapp (fun s => (x s)%:P + (y s - x s) *: 'X) 0 (pat i j)).

Lemma line_detE x y n (pat : 'I_n -> 'I_n -> option sigma) t :
  (line_det x y pat).[t] = \det (pattern_mx pat (fun s => x s + (y s - x s) * t)).
Proof.
rewrite -horner_evalE -det_map_mx; congr (\det _); apply/matrixP => i j; rewrite !mxE.
by case: (pat i j) => [s|] /=; rewrite horner_evalE ?horner0 // hornerD hornerC hornerZ hornerX.
Qed.

(** Paper, Section 3; Lean [exists_simultaneous_det_ne_zero_of_witness] (GenericRank.lean),
    with the line [x + t (y - x)] in place of multivariate polynomials. *)
Theorem common_nonvanishing (kappa : finType) (n : kappa -> nat)
    (pat : forall k, 'I_(n k) -> 'I_(n k) -> option sigma) :
  (forall k, exists x, \det (pattern_mx (pat k) x) != 0) ->
  exists x, forall k, \det (pattern_mx (pat k) x) != 0.
Proof.
move=> wit.
suff [x hx] : exists x, forall k, k \in enum kappa -> \det (pattern_mx (pat k) x) != 0.
  by exists x => k; apply: hx; rewrite mem_enum.
elim: (enum kappa) => [|k r [x hx]]; first by exists (fun=> 0).
have [y hy] := wit k; pose Q := \prod_(k' <- k :: r) line_det x y (pat k').
have L1 k' : (line_det x y (pat k')).[1] = \det (pattern_mx (pat k') y).
  by rewrite line_detE (@eq_pattern_mx _ _ _ y) // => s; rewrite mulr1 addrC subrK.
have L0 k' : (line_det x y (pat k')).[0] = \det (pattern_mx (pat k') x).
  by rewrite line_detE (@eq_pattern_mx _ _ _ x) // => s; rewrite mulr0 addr0.
have Q0 : Q != 0.
  rewrite prodf_seq_neq0; apply/allP => k' /predU1P[->|k'r] /=.
    by apply: contraNneq hy => P0; rewrite -L1 P0 horner0.
  by apply: contraNneq (hx k' k'r) => P0; rewrite -L0 P0 horner0.
(* [Q] has at most [size Q - 1] roots: one of the integers [0, ..., size Q - 1] is not a root. *)
have uQ : uniq [seq (i%:R : rat) | i <- iota 0 (size Q)].
  by rewrite map_inj_uniq ?iota_uniq // => a b /eqP; rewrite eqr_nat => /eqP.
have : ~~ all (root Q) [seq i%:R | i <- iota 0 (size Q)].
  by apply/negP => /(max_poly_roots Q0)/(_ uQ); rewrite size_map size_iota ltnn.
rewrite -has_predC => /hasP[t _ /= Qt]; exists (fun s => x s + (y s - x s) * t) => k' k'r.
move: Qt; rewrite rootE /Q horner_prod prodf_seq_neq0 => /allP /(_ k' k'r) /=.
by rewrite line_detE.
Qed.

End Patterns.

(** A pattern whose diagonal entries are variables, each variable occurring at most once, has a
    nonzero determinant at the assignment that is 1 on the diagonal variables and 0 elsewhere
    (the matrix is then the identity). *)
Lemma pattern_witness (sigma : eqType) n (pat : 'I_n -> 'I_n -> option sigma) :
  (forall i, pat i i != None) ->
  (forall i j i' j', pat i j != None -> pat i j = pat i' j' -> i = i' /\ j = j') ->
  exists x, \det (pattern_mx pat x) != 0.
Proof.
move=> diag uniq; pose x s : rat := ([exists i, pat i i == Some s])%:R; exists x.
suff -> : pattern_mx pat x = 1%:M by rewrite det1 oner_neq0.
apply/matrixP => i j; rewrite !mxE; case: eqVneq => [<-|ij].
  case E: (pat i i) (diag i) => [s|] //= _.
  by rewrite /x (_ : [exists _, _] = true) //; apply/existsP; exists i; rewrite E.
case E: (pat i j) => [s|] //=; rewrite /x (_ : [exists _, _] = false) //.
apply/negbTE/existsP => -[k /eqP Ek].
have [ik jk] : i = k /\ j = k by apply: uniq; rewrite E ?Ek.
by rewrite ik jk eqxx in ij.
Qed.

(** ** Independent rows *)

(** The rows of [M] indexed by [S] are linearly independent. *)
Definition free_rows m n (M : 'M[rat]_(m, n)) (S : {set 'I_m}) : Prop :=
  forall u : 'rV[rat]_m, (forall i, i \notin S -> u 0 i = 0) -> u *m M = 0 -> u = 0.

Lemma free_rows_sub m n (M : 'M[rat]_(m, n)) (S S' : {set 'I_m}) :
  S' \subset S -> free_rows M S -> free_rows M S'.
Proof. by move=> SS fS u uS; apply: fS => i iS; apply: uS; exact: contra (subsetP SS i) iS. Qed.

Section FreeRows.
Variables (m n k : nat) (M : 'M[rat]_(m, n)) (r : 'I_k -> 'I_m).

(** [v *m rowsub r 1] spreads [v] on the rows [r l]. *)
Lemma spread_out (v : 'rV[rat]_k) i :
  i \notin [set r l | l in 'I_k] -> (v *m rowsub r 1%:M) 0 i = 0.
Proof.
move=> ni; rewrite mxE big1 // => l _; rewrite !mxE.
by case: eqVneq ni => [<-|]; rewrite ?mulr0 ?imset_f.
Qed.

Lemma spread_in (v : 'rV[rat]_k) l :
  injective r -> (v *m rowsub r 1%:M) 0 (r l) = v 0 l.
Proof.
move=> rI; rewrite mxE (bigD1 l) //= big1 ?addr0; last by rewrite !mxE eqxx mulr1.
by move=> l' l'l; rewrite !mxE inj_eq // (negPf l'l) mulr0.
Qed.

(** For an injective row map, free rows mean that [rowsub r M] has full row rank. *)
Lemma free_rowsP : injective r ->
  free_rows M [set r l | l in 'I_k] <-> (forall v : 'rV[rat]_k, v *m rowsub r M = 0 -> v = 0).
Proof.
have subM (v : 'rV[rat]_k) : v *m rowsub r M = (v *m rowsub r 1%:M) *m M.
  by rewrite -mulmxA mul_rowsub_mx mul1mx.
move=> rI; split => [free v vM | free u supp uM].
  have u0 : v *m rowsub r 1%:M = 0 by apply: free; [exact: spread_out | rewrite -subM].
  by apply/rowP => l; rewrite -(spread_in v l rI) u0 !mxE.
have uE : u = (\row_l u 0 (r l)) *m rowsub r 1%:M.
  apply/rowP => i; case: (boolP (i \in [set r l | l in 'I_k])) => [/imsetP[l _ ->]|ni].
    by rewrite spread_in // mxE.
  by rewrite spread_out // supp.
by rewrite uE (free (\row_l u 0 (r l))) ?mul0mx // subM -uE.
Qed.

(** Two equal rows make a minor vanish. *)
Lemma minor_inj (c : 'I_k -> 'I_n) :
  \det (\matrix_(i, j) M (r i) (c j)) != 0 -> injective r.
Proof.
move=> det0 i i' ri; apply/eqP; apply: contraNT det0 => ii'; apply/eqP.
by apply: (determinant_alternate ii') => j; rewrite !mxE ri.
Qed.

End FreeRows.

Lemma free_rows_rank m n (M : 'M[rat]_(m, n)) (S : {set 'I_m}) :
  free_rows M S -> (#|S| <= \rank M)%N.
Proof.
have SE : S = [set idx i | i in 'I_#|S|].
  apply/setP => i; apply/idP/imsetP => [/idx_onto[l <-]|[l _ ->]]; [by exists l | exact: idxP].
rewrite {1}SE => /(free_rowsP M (@idx_inj _ S)) /inj_row_free /eqP <-.
by rewrite -[M in rowsub _ M]mul1mx -mul_rowsub_mx mxrankM_maxr.
Qed.

(** A nonzero square minor makes its rows independent (its row map [r] is then injective). *)
Lemma minor_free_rows m n k (M : 'M[rat]_(m, n)) (r : 'I_k -> 'I_m) (c : 'I_k -> 'I_n) :
  \det (\matrix_(i, j) M (r i) (c j)) != 0 -> free_rows M [set r i | i in 'I_k].
Proof.
move=> det0; apply/(free_rowsP M (minor_inj det0)) => v vM.
have U : \matrix_(i, j) M (r i) (c j) \in unitmx by rewrite unitmxE unitfE.
rewrite -(mulmxK U v) (_ : v *m _ = 0) ?mul0mx //.
have -> : \matrix_(i, j) M (r i) (c j) = colsub c (rowsub r M).
  by apply/matrixP => i j; rewrite !mxE.
by rewrite mulmx_colsub vM; apply/matrixP => i j; rewrite !mxE.
Qed.

(** A nonzero square minor of size [k] gives rank at least [k]. *)
Lemma minor_rank m n k (M : 'M[rat]_(m, n)) (r : 'I_k -> 'I_m) (c : 'I_k -> 'I_n) :
  \det (\matrix_(i, j) M (r i) (c j)) != 0 -> (k <= \rank M)%N.
Proof.
move=> det0; have := free_rows_rank (minor_free_rows det0).
by rewrite card_imset ?card_ord //; exact: minor_inj det0.
Qed.

(** Rows split into blocks: the nonzero entries of a row of key [br i] lie in columns of the same
    key.  If the rows of [S] of each key are independent, all the rows of [S] are. *)
Lemma free_rows_blocks m n (M : 'M[rat]_(m, n)) (K : eqType) (br : 'I_m -> K) (bc : 'I_n -> K)
    (S : {set 'I_m}) :
  (forall i j, M i j != 0 -> br i = bc j) ->
  (forall k : K, free_rows M [set i in S | br i == k]) ->
  free_rows M S.
Proof.
move=> blocks free u supp uM; apply/rowP => i; rewrite mxE.
(* The part [v] of [u] on the rows of key [br i] is a vanishing combination of rows. *)
pose v := \row_i' (if br i' == br i then u 0 i' else 0).
suff /rowP/(_ i) : v = 0 by rewrite !mxE eqxx.
apply: (free (br i)) => [i'|].
  by rewrite inE mxE; case: eqP; rewrite ?andbT ?eqxx // => _ /supp.
apply/rowP => j; rewrite !mxE.
have E i' : v 0 i' * M i' j = (bc j == br i)%:R * (u 0 i' * M i' j).
  rewrite mxE; have [->|/blocks ->] := eqVneq (M i' j) 0; first by rewrite !mulr0.
  by case: eqP; rewrite ?mul1r ?mul0r.
rewrite (eq_bigr _ (fun i' _ => E i')) -mulr_sumr.
by move/rowP/(_ j): uM; rewrite !mxE => ->; rewrite mulr0.
Qed.

(** The rank of a sum is at most the sum of the ranks. *)
Lemma mxrank_sum (I : Type) (rs : seq I) (P : pred I) m n (B : I -> 'M[rat]_(m, n)) :
  (\rank (\sum_(i <- rs | P i) B i)%R <= \sum_(i <- rs | P i) \rank (B i))%N.
Proof.
apply: (big_ind2 (fun (A : 'M[rat]_(m, n)) k => \rank A <= k)%N) => // [|A1 k1 A2 k2 h1 h2].
  by rewrite mxrank0.
exact: leq_trans (mxrank_add _ _) (leq_add h1 h2).
Qed.

(** The diagonal 0/1 matrix of a set [s] has rank at most [#|s|]. *)
Lemma rank_diag_set m (s : {set 'I_m}) :
  (\rank (diag_mx (\row_i (i \in s)%:R : 'rV[rat]_m)) <= #|s|)%N.
Proof.
have -> : diag_mx (\row_i (i \in s)%:R) = (\sum_(i in s) delta_mx i i : 'M[rat]_m)%R.
  apply/matrixP => i j; rewrite summxE !mxE; case: eqVneq => [<-|ij].
    rewrite (big_mkcond (fun i0 => i0 \in s)) (bigD1 i) //= big1.
      by move=> i0 i0i; rewrite !mxE eq_sym (negPf i0i); case: ifP.
    by rewrite !mxE eqxx addr0 mulr1n; case: ifP.
  rewrite mulr0n big1 // => i0 _; rewrite mxE.
  by case: (i =P i0) => // ii0; rewrite -ii0 eq_sym (negPf ij).
by rewrite (leq_trans (mxrank_sum _ _ _)) // -sum1_card leq_sum // => i _; rewrite mxrank_delta.
Qed.

(** The rank is at most the size of a cover of the nonzero entries by rows and columns. *)
Lemma rank_le_cover m n (A : 'M[rat]_(m, n)) (s : {set 'I_m}) (t : {set 'I_n}) :
  (forall i j, A i j != 0 -> (i \in s) || (j \in t)) -> (\rank A <= #|s| + #|t|)%N.
Proof.
move=> cover; pose Ds := diag_mx (\row_i (i \in s)%:R : 'rV[rat]_m).
pose Dt := diag_mx (\row_j (j \in t)%:R : 'rV[rat]_n).
(* The rows of [s], plus the rest, which lives in the columns of [t]. *)
have -> : A = Ds *m A + (A - Ds *m A) *m Dt.
  apply/matrixP => i j; rewrite /Ds /Dt mul_mx_diag mul_diag_mx !mxE.
  case: (boolP (i \in s)) => si; first by rewrite mul1r subrr mul0r addr0.
  have [->|/cover] := eqVneq (A i j) 0; first by rewrite !(mulr0, mul0r, subr0, addr0).
  by rewrite (negPf si) /= => ->; rewrite mul0r add0r subr0 mulr1.
rewrite (leq_trans (mxrank_add _ _)) // leq_add //.
  exact: leq_trans (mxrankM_maxl _ _) (rank_diag_set s).
exact: leq_trans (mxrankM_maxr _ _) (rank_diag_set t).
Qed.
