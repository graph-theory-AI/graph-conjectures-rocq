(** * The number of partitions of the hypercube into squares is d^((1+o(1)) 2^(d-1))

Let f_2(d) be the number of partitions of Q_d into squares and M(m) the number of matchings of
squares of Q_m (sets of pairwise disjoint squares).
- [upper_bound.v]: f_2(d) <= (2 d^2)^(2^(d-2)), by counting the sets of 2^(d-2) squares.
- [gluing.v]: M(m)^4 <= 2^(4 2^m) f_2(m+2), by a product construction (lifting lemma).
- [nibble.v]: M(m) >= m^((1-o(1)) 2^(m-1)), by a nibble where each round uses only the squares
  whose free coordinates are in a group of coordinates reserved for this round, so that
  independence is exact and no concentration inequality is needed.

The lifting lemma comes from Graph-Theory-LLM-Proofs (attacks/2401.00299__02), where the lower
bound on M(m) is cited from the article of Alon, Balogh and Potapov, who deduce it from a theorem
of Asratian and Kuzjurin.  The nibble on groups of coordinates comes from graph-theory-rocq
(packing-theory/theories/applications/hypercube_square_partitions). *)

From GraphTheory Require Import digraph sgraph.
From GC.packing.AX_hypercube_subcube_partitions_dimension_2_asymptotics
  Require Import squares upper_bound gluing nibble.
From GC.packing.AX_hypercube_subcube_partitions_dimension_2_asymptotics Require main.
From mathcomp Require Import boot zify.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma leq_exp2r_imp a b e : a <= b -> a ^ e <= b ^ e.
Proof. by case: e => // e le_ab; rewrite leq_exp2r. Qed.

(** f_2(m+2) >= (m+2)^((1-1/K) 2^(m+1)) / c^(2^m/K), where c depends only on K. *)
Lemma lower_bound K : 0 < K -> exists c m0, forall m, m0 <= m ->
  m.+2 ^ (2 * K.-1 * 2 ^ m) <= c ^ (2 ^ m) * square_partition_count m.+2 ^ K.
Proof.
move=> K0; have [R RE] : exists R, R = 256 * K ^ 4 by eexists.
have R0 : 0 < R by rewrite RE muln_gt0 expn_gt0 K0.
exists ((9 * R ^ 2 * 2 ^ 8) ^ K), (2 * R) => m le_m; set f := square_partition_count _.
set D := 2 ^ m; have D0 : 0 < D by rewrite expn_gt0.
pose n := m %/ R; have n1 : 1 < n by rewrite leq_divRL.
pose P := 8 * 'C(n, 2).
have leP : m.+2 ^ 2 <= 9 * R ^ 2 * P.
  have le_m3 : m.+2 <= 3 * R * n by have := ltn_ceil m R0; rewrite -/n; nia.
  have le_n : n ^ 2 <= P by have := mul_bin_diag n 1; rewrite bin1 /P; nia.
  rewrite (leq_trans (leq_exp2r_imp 2 le_m3)) // expnMn (expnMn 3) leq_mul2l le_n orbT //.
have leW : P ^ (K.-1 * D) <= (2 ^ 8) ^ (K * D) * f ^ K.
  have mE : m = 256 * K ^ 4 * n + m %% R by rewrite -RE mulnC -divn_eq.
  apply: leq_trans (many_matchings K0 n1 mE) _; rewrite expnM expnMn.
  rewrite (leq_trans (leq_exp2r_imp K (leq_mul (leqnn _) (lifting m)))) // mulnA expnMn.
  rewrite leq_mul2r -expnD -!expnM leq_pexp2l ?orbT //; nia.
rewrite -mulnA expnM (leq_trans (leq_exp2r_imp _ leP)) // expnMn.
rewrite (leq_trans (leq_mul (leqnn _) leW)) // mulnA -(expnM (9 * R ^ 2 * 2 ^ 8)).
rewrite [in leqRHS]expnMn !leq_mul // leq_pexp2l ?muln_gt0 ?expn_gt0 ?R0 //.
by rewrite leq_mul2r leq_pred orbT.
Qed.

Theorem asymptotics : main.AX_hypercube_subcube_partitions_dimension_2_asymptotics.
Proof.
move=> q q0; have [c [m0 low]] := @lower_bound (2 * q) (ltac:(lia)).
exists (m0 + c + 2 ^ q).+2 => -[|[|m]] // le_d; set f := main.square_partition_count _.
have dE : 2 ^ (m.+2 - 1) = 2 * 2 ^ m by rewrite subn1 expnS.
rewrite dE; set D := 2 ^ m; have D0 : 0 < D by rewrite expn_gt0.
split.
  rewrite -(@leq_exp2r _ _ 2) // -!expnM [q * 2]mulnC.
  have le_cd : c ^ D <= m.+2 ^ (2 * D).
    by rewrite expnM leq_exp2r // expnS; nia.
  have := low m (ltac:(lia)); rewrite -/f -/D => le_f.
  have pow0 : 0 < m.+2 ^ (2 * D) by rewrite expn_gt0.
  rewrite -(leq_pmul2l pow0) -expnD.
  have -> : 2 * D + (q - 1) * (2 * D) * 2 = 2 * (2 * q).-1 * D by nia.
  by rewrite (leq_trans le_f) // leq_mul2r le_cd orbT.
rewrite (leq_trans (leq_exp2r_imp q (upper_bound m))) // expnAC mulnA expnM leq_exp2r //.
by rewrite expnMn -expnM mulnDl expnD [2 * q]mulnC mulnC leq_mul2l expnS; nia.
Qed.
