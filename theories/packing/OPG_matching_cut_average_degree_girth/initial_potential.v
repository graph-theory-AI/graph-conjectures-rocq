(** * The initial potential

The potential of greedy.v for edges from each vertex taken d + 2 times as a source.  The coefficient
of a set of a vertices is the inverse of [threshold n a] = (4n)^((d + 1) a) a^a, up to the factor
[total n].  When no edge has been added, the total contribution of the sets of a <= n/2 vertices is
'C(n, a) (6a)^((d + 2) a) / [threshold n a] <= 2^-a if d is large enough [count_small], from
'C(n, a) <= (4n/a)^a [bin_le].  So the potential is less than 1, that is [total n]. *)

From mathcomp Require Import boot zify.
From GC.packing.OPG_matching_cut_average_degree_girth Require Import greedy.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Inequalities *)

Lemma bernoulli a k : k <= a.+1 -> (a.+1 - k) * a.+1 ^ k <= a ^ k * a.+1.
Proof.
elim: k => [|k IH ka]; first by rewrite !expn0 subn0 muln1 mul1n.
have := IH (ltnW ka); rewrite !expnS; move: (a ^ k) (a.+1 ^ k) => u v {}IH.
have : a * ((a.+1 - k) * v) <= a * (u * a.+1) by rewrite leq_mul2l IH orbT.
nia.
Qed.

Lemma expnS_le4 a : a.+1 ^ a <= 4 * a ^ a.
Proof.
case: a => // a; set b := a.+1.
have := @bernoulli b (uphalf b); set k := uphalf b => B.
have kb : k <= b.+1 by rewrite /k; lia.
have {}B : b.+1 ^ k <= 2 * b ^ k.
  rewrite -(@leq_pmul2r b.+1) //; have := B kb; have : b.+1 <= 2 * (b.+1 - k) by rewrite /k; lia.
  move: (b ^ k) (b.+1 ^ k) => u v; nia.
have {}B : b.+1 ^ (k + k) <= 4 * b ^ (k + k) by rewrite !expnD; nia.
have [e|e] : k + k = b \/ k + k = b.+1 by rewrite /k; lia.
  by rewrite -{2 4}e.
by move: B; rewrite e !expnS; move: (b ^ b) (b.+1 ^ b) => u v; nia.
Qed.

Lemma bin_le n a : 'C(n, a) * a ^ a <= (4 * n) ^ a.
Proof.
elim: a => [|a IH]; first by rewrite bin0.
rewrite expnS mulnA [_ * a.+1]mulnC mul_bin_left expnS.
apply: (@leq_trans (n * 'C(n, a) * (4 * a ^ a))).
  by rewrite leq_mul ?expnS_le4 // leq_mul // leq_subr.
have : n * ('C(n, a) * a ^ a) <= n * (4 * n) ^ a by rewrite leq_mul2l IH orbT.
by move: ('C(n, a)) (a ^ a) (_ ^ a) => u v w; nia.
Qed.

Lemma sum_half t T m : 0 < T -> (forall a, 0 < a -> t a * 2 ^ a <= T) ->
  \sum_(1 <= a < m.+1) t a < T.
Proof.
move=> T0 tT; rewrite -(@ltn_pmul2r (2 ^ m)) ?expn_gt0 //.
suff : (\sum_(1 <= a < m.+1) t a) * 2 ^ m + T <= T * 2 ^ m by lia.
elim: m => [|m IH]; first by rewrite big_geq // mul0n muln1.
rewrite big_nat_recr //= mulnDl; have := tT m.+1 isT.
by rewrite !expnS; move: (2 ^ m) (\sum_(1 <= _ < _) _) (t _) IH => u v w; nia.
Qed.

(** ** The potential *)

Section InitialPotential.

(** Each vertex has [d.+2] outgoing edges. *)
Variable d : nat.
Hypothesis large_d : 6 ^ d.+2 * 8 <= 4 ^ d.+1 * 2 ^ d.

(** A lower bound on the product of the weights of the edges from a set of [a] vertices with at
    most one edge leaving the set from each vertex. *)
Definition threshold n a := (4 * n) ^ (d.+1 * a) * a ^ a.

(** The coefficients of the potential are normalised by [coeff n a * threshold n a = total n]. *)
Definition total n := \prod_(1 <= b < n.+1) threshold n b.
Definition coeff n a := \prod_(1 <= b < n.+1 | b != a) threshold n b.

Lemma total_gt0 n : 0 < total n.
Proof.
rewrite /total big_nat prodn_cond_gt0 // => b /andP[b0 bn].
by rewrite muln_gt0 !expn_gt0 b0 muln_gt0 (leq_trans b0 bn).
Qed.

Lemma coeffE n a : 0 < a <= n -> coeff n a * threshold n a = total n.
Proof.
move=> an; rewrite /total (bigD1_seq a) ?mem_index_iota ?iota_uniq //=.
exact: mulnC.
Qed.

Lemma count_small n a : 0 < a -> 2 * a <= n ->
  'C(n, a) * (6 * a) ^ (d.+2 * a) * 2 ^ a <= threshold n a.
Proof.
move=> a0 an; rewrite -(@leq_pmul2l (a ^ a)) ?expn_gt0 ?a0 //.
apply: (@leq_trans ((4 * n) ^ a * ((6 * a) ^ (d.+2 * a) * 2 ^ a))).
  by rewrite -mulnA mulnCA mulnA leq_mul2r bin_le orbT.
rewrite /threshold !expnM mulnCA -!expnMn leq_exp2r //.
have ad : (2 * a) ^ d <= n ^ d by case: (d) => // k; rewrite leq_exp2r.
move: ad large_d; rewrite !expnMn !expnS.
move: (6 ^ d) (4 ^ d) (2 ^ d) (a ^ d) (n ^ d) => p q r u w ad num.
have le : 288 * p * u <= 4 * q * w by nia.
have := leq_mul (leqnn (n * (a * a))) le; nia.
Qed.

(** The sources of the edges. *)
Definition sources n : seq 'I_n := flatten (nseq d.+2 (enum 'I_n)).

Lemma count_sources n (A : {set 'I_n}) : count (mem A) (sources n) = d.+2 * #|A|.
Proof. by rewrite count_flatten map_nseq sumn_nseq mulnC cardE size_filter enumT. Qed.

Lemma count_mem_sources n x : count_mem x (sources n) = d.+2.
Proof.
by rewrite count_flatten map_nseq sumn_nseq count_uniq_mem ?enum_uniq // mem_enum mul1n.
Qed.

Lemma initial_potential n : potential (coeff n) [::] (sources n) < total n.
Proof.
rewrite /potential; pose F a := coeff n a * (6 * a) ^ (d.+2 * a).
under eq_bigr do rewrite big_nil muln1 count_sources -/(F _).
have -> : \sum_(A : {set 'I_n} | small A) F #|A| =
          \sum_(1 <= a < n.+1) if 2 * a <= n then 'C(n, a) * F a else 0.
  rewrite big_geq_mkord [RHS]big_mkcond /=.
  rewrite (partition_big (fun A : {set 'I_n} => inord #|A| : 'I_n.+1) xpredT) //=.
  apply: eq_bigr => a _.
  have e (A : {set 'I_n}) : small A && (inord #|A| == a) =
      (A \in [set B : {set 'I_n} | #|B| == a]) && ((0 < a) && (2 * a <= n)).
    have An : #|A| < n.+1 by rewrite ltnS -[X in _ <= X](card_ord n) max_card.
    rewrite inE -val_eqE /= inordK //.
    by rewrite andbC /small; have [->|] := eqVneq #|A| a.
  rewrite (eq_bigl _ _ e); case: (0 < a); last by rewrite big_pred0 // => A; rewrite !andbF.
  case: leqP => _; last by rewrite big_pred0 // => A; rewrite !andbF.
  rewrite (eq_bigl (fun A => A \in [set B : {set 'I_n} | #|B| == a])) => [A|].
    exact: andbT.
  rewrite (eq_bigr (fun=> F a)) => [A|]; first by rewrite inE => /eqP->.
  by rewrite sum_nat_const card_draws card_ord.
apply: sum_half (total_gt0 n) _ => a a0; case: ifP => // an.
rewrite -(@coeffE n a) ?a0 /F; first by lia.
by rewrite mulnCA -mulnA leq_mul2l count_small ?orbT.
Qed.

End InitialPotential.
