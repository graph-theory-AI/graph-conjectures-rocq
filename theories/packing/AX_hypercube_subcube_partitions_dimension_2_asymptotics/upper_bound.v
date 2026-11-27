(** * Upper bound on the number of square partitions

A partition of Q_d into squares is a set of s = 2^(d-2) squares, among the s C(d,2) squares of
Q_d.  As C(n,s) <= (4n/s)^s, this gives f_2(d) <= (4 C(d,2))^s <= (2 d^2)^s. *)

From GraphTheory Require Import digraph sgraph.
From GC.packing.AX_hypercube_subcube_partitions_dimension_2_asymptotics Require Import squares.
From mathcomp Require Import boot zify_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma leq_ffact_exp n s : n ^_ s <= n ^ s.
Proof.
rewrite ffact_prod -iter_muln_1 -big_const_ord; apply: leq_prod => i _; exact: leq_subr.
Qed.

Lemma leq_exp_fact s : s ^ s <= 4 ^ s * s`!.
Proof.
have le_bin : 'C(2 * s, s) <= 4 ^ s.
  rewrite -(expnM 2 2) -(card_ord (2 * s)) -card_draws -[X in _ ^ X]cardsT -card_powerset.
  by rewrite subset_leq_card // powersetT subsetT.
apply: leq_trans (leq_mul le_bin (leqnn _)).
rewrite bin_ffact ffact_prod -iter_muln_1 -big_const_ord.
by apply: leq_prod => i _; rewrite mulSn mul1n -addnBA ?leq_addr // ltnW.
Qed.

Lemma leq_bin_exp n s : 'C(n, s) * s ^ s <= (4 * n) ^ s.
Proof.
rewrite (leq_trans (leq_mul (leqnn _) (leq_exp_fact s))) // mulnCA bin_ffact expnMn.
by rewrite leq_mul2l leq_ffact_exp orbT.
Qed.

Theorem upper_bound d : square_partition_count d.+2 <= (2 * d.+2 ^ 2) ^ 2 ^ d.
Proof.
have squaresE : #|squares d.+2| = 2 ^ d * 'C(d.+2, 2).
  by have := card_squares d.+2; rewrite !expnS; lia.
apply: (@leq_trans 'C(#|squares d.+2|, 2 ^ d)).
  rewrite -cards_draws; apply/subset_leq_card/subsetP => P.
  rewrite !inE => /andP[partP /forall_inP sqP].
  have Psq : P \subset squares d.+2 by apply/subsetP => S /sqP; rewrite inE.
  have matP : P \in matchings d.+2 by apply/matchingP; split=> //; case/and3P: partP.
  have := card_matching matP; rewrite (cover_partition partP) cardsT card_hypercube Psq.
  by rewrite !expnS /=; lia.
rewrite -(@leq_pmul2r ((2 ^ d) ^ 2 ^ d)) ?expn_gt0 // (leq_trans (leq_bin_exp _ _)) //.
rewrite squaresE -expnMn leq_exp2r ?expn_gt0 //.
have := mul_bin_diag d.+2 1; rewrite bin1; nia.
Qed.
