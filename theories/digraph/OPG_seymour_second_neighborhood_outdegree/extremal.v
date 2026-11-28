(** * The extremal contradiction

Proposition 4.1 of the paper of OpenAI: no nonempty oriented digraph with positive in-degrees
satisfies the strict subset growth.

Proof.  Among the pairs (P, Q) of conflict-free families containing the diagonal (the pair
(diagonal, diagonal) is one, by orientation), take one maximizing |P| + |Q| + d, where d is the
number of points outside F_1(P) u F_2(Q).  The columns of P and the rows of Q are nonempty
proper sets, so summing the strict growth over them gives
|P| + |F_1^2(P)| < 2 |F_1(P)| and |Q| + |F_2^2(Q)| < 2 |F_2(Q)|.  The complements
R = ~: F_2^2(Q) and C = ~: F_1^2(P) satisfy |R| + |C| > |P| + |Q| + 2d, contain the diagonal,
whose members are conflict-free, and the corners H of their conflicts are uncovered by P and Q,
so |H| <= d.  The pruning lemma gives conflict-free P' in R and Q' in C containing the
diagonal, with |P'| + |Q'| + d' >= |R| + |C| - d - d' + d' > |P| + |Q| + d: a contradiction.

Provenance: the paper "A proof of Seymour's second-neighborhood conjecture" of OpenAI, a
model-generated manuscript that is not peer reviewed,
https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/preprints/A-proof-of-Seymours-second-neighborhood-conjecture-September-23-2026/paper.pdf
and its Lean formalization (ExtremalImages.lean, ExtremalCompatibility.lean, ExtremalCounting.lean,
ExtremalContradiction.lean),
https://github.com/openai/math/tree/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Combinatorics/SecondNeighborhood
which proves the full statement of the conjecture. *)

From GraphTheory Require Import digraph.
From GC.digraph.OPG_seymour_second_neighborhood_outdegree Require Import defs pruning.
From mathcomp Require Import boot zify_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Extremal.
Variable G : diGraph.
Implicit Types (P Q : {set G * G}).

(** The column of [P] at [j] and the row of [Q] at [i]. *)
Definition column P (j : G) : {set G} := [set p | (p, j) \in P].
Definition row Q (i : G) : {set G} := [set s | (i, s) \in Q].

Lemma card_columns P : #|P| = \sum_j #|column P j|.
Proof.
rewrite -sum1_card big_mkcond (eq_bigr (fun z => if (z.1, z.2) \in P then 1 else 0));
  first [by case | idtac].
rewrite -(pair_bigA _ (fun p j => if (p, j) \in P then 1 else 0)) exchange_big.
by apply: eq_bigr => j _; rewrite -sum1_card [RHS]big_mkcond; apply: eq_bigr => p _; rewrite inE.
Qed.

Lemma card_rows Q : #|Q| = \sum_i #|row Q i|.
Proof.
rewrite -sum1_card big_mkcond (eq_bigr (fun z => if (z.1, z.2) \in Q then 1 else 0));
  first [by case | idtac].
rewrite -(pair_bigA _ (fun i s => if (i, s) \in Q then 1 else 0)).
by apply: eq_bigr => i _; rewrite -sum1_card [RHS]big_mkcond; apply: eq_bigr => s _; rewrite inE.
Qed.

(** F_1 acts on each column as F, and F_2 on each row. *)
Lemma column_left_image P j : column (left_image P) j = NS(column P j).
Proof. by apply/setP => i; rewrite in_NS !inE; apply: eq_existsb => p; rewrite inE. Qed.

Lemma row_right_image Q i : row (right_image Q) i = NS(row Q i).
Proof. by apply/setP => j; rewrite in_NS !inE; apply: eq_existsb => s; rewrite inE. Qed.

(** The objective of the extremal choice. *)
Definition objective P Q : nat := #|P| + #|Q| + #|~: (left_image P :|: right_image Q)|.

(** Admissible pairs: conflict-free, containing the diagonal. *)
Definition admissible P Q : bool :=
  [&& conflict_free P Q, diagonal G \subset P & diagonal G \subset Q].

Lemma diagonal_admissible : oriented G -> admissible (diagonal G) (diagonal G).
Proof.
move=> oG; rewrite /admissible subxx !andbT; apply/conflict_freeP => -[v w] [x y].
rewrite !inE /conflict /= => /eqP <- /eqP <-.
by apply/negP => /andP[/oG/negbTE->].
Qed.

(** Summing the strict growth over a family of nonempty proper sets indexed by [G]. *)
Lemma sum_growth (S : G -> {set G}) :
  0 < #|G| -> strict_growth G -> (forall j, S j != set0) -> (forall j, S j != setT) ->
  \sum_j #|S j| + \sum_j #|NS(NS(S j))| < 2 * \sum_j #|NS(S j)|.
Proof.
move=> /card_gt0P[j0 _] sg S0 ST; rewrite -big_split big_distrr /= (bigD1 j0) //=.
rewrite [X in _ < X](bigD1 j0) //= -addSn; apply: leq_add; first exact: sg.
by apply: leq_sum => j _; apply: ltnW; apply: sg.
Qed.

(** Inequalities (18): the columns of [P] and the rows of [Q] are nonempty proper sets. *)
Lemma admissible_growth P Q :
  0 < #|G| -> positive_indeg G -> strict_growth G -> admissible P Q ->
  #|P| + #|left_image (left_image P)| < 2 * #|left_image P| /\
  #|Q| + #|right_image (right_image Q)| < 2 * #|right_image Q|.
Proof.
move=> G0 pos sg /and3P[/conflict_freeP cf /subsetP dP /subsetP dQ].
have vv v : (v, v) \in diagonal G by rewrite inE.
split.
  rewrite !card_columns; under [X in _ + X]eq_bigr do rewrite !column_left_image.
  under [X in _ < 2 * X]eq_bigr do rewrite column_left_image.
  apply: sum_growth => // j; apply/eqP => cT.
    by move: (in_set0 j); rewrite -cT inE dP.
  have [w wj] := pos j; have [p pw] := pos w.
  have pj : (p, j) \in P by move: (in_setT p); rewrite -cT inE.
  by move: (cf _ _ pj (dQ _ (vv w))); rewrite /conflict pw wj.
rewrite !card_rows; under [X in _ + X]eq_bigr do rewrite !row_right_image.
under [X in _ < 2 * X]eq_bigr do rewrite row_right_image.
apply: sum_growth => // i; apply/eqP => rT.
  by move: (in_set0 i); rewrite -rT inE dQ.
have [w wi] := pos i; have [s sw] := pos w.
have is_ : (i, s) \in Q by move: (in_setT s); rewrite -rT inE.
by move: (cf _ _ (dP _ (vv w)) is_); rewrite /conflict wi sw.
Qed.

(** Inequality (20): the corners (p,s) of the conflicts of the complements are uncovered. *)
Lemma Hset_uncovered P Q :
  Hset (~: right_image (right_image Q)) (~: left_image (left_image P))
    \subset ~: (left_image P :|: right_image Q).
Proof.
apply/subsetP => -[p s]; rewrite inE => /existsP[i /existsP[j /and4P[]]] /=.
rewrite !in_setC in_right_image in_left_image !negb_exists /=.
move=> /forallP pjR /forallP isC pi sj; rewrite in_setU negb_or.
by apply/andP; split; apply/negP => h; [move: (isC p) | move: (pjR s)]; rewrite h ?pi ?sj.
Qed.

(** The pruning of the complements gives an admissible pair: the diagonal members belong to the
    complements and conflict with none of their members, so they are retained. *)
Lemma pruning_admissible P Q R' C' :
  admissible P Q ->
  pruning_result (~: right_image (right_image Q)) (~: left_image (left_image P)) R' C' ->
  admissible R' C'.
Proof.
move=> /and3P[]; rewrite conflict_free_disjoint => /disjointFr img /subsetP dP /subsetP dQ.
case=> _ cf' keepR keepC _.
(* the diagonal of P (of Q) gives (v,u) in F_1 P (and (u,v) in F_2 Q) for every arc u -- v *)
have F1d u v : u -- v -> (v, u) \in left_image P.
  by move=> uv; rewrite inE; apply/existsP; exists u; rewrite dP ?inE.
have F2d u v : u -- v -> (u, v) \in right_image Q.
  by move=> uv; rewrite inE; apply/existsP; exists u; rewrite dQ ?inE.
rewrite /admissible cf' /=; apply/andP; split; apply/subsetP => -[v w];
  rewrite inE /= => /eqP <-.
- apply: keepR.
    by rewrite in_setC in_right_image /=; apply/existsP => -[s /andP[vs /F1d/img]]; rewrite vs.
  apply/forall_inP => -[i s]; rewrite in_setC in_left_image /conflict /= => /negP isC.
  by apply/negP => /andP[vi sv]; apply: isC; apply/existsP; exists v; rewrite F1d.
- apply: keepC.
    by rewrite in_setC in_left_image /=; apply/existsP => -[p /andP[/img pv /F2d]]; rewrite pv.
  apply/forall_inP => -[p j]; rewrite in_setC in_right_image /conflict /= => /negP pjR.
  by apply/negP => /andP[pv vj]; apply: pjR; apply/existsP; exists v; rewrite F2d.
Qed.

(** Proposition 4.1. *)
Theorem no_strict_growth :
  oriented G -> 0 < #|G| -> positive_indeg G -> strict_growth G -> False.
Proof.
move=> oG G0 pos sg.
case: (@arg_maxnP _ (diagonal G, diagonal G) (fun pq => admissible pq.1 pq.2)
         (fun pq => objective pq.1 pq.2) (diagonal_admissible oG)) => -[P Q] /= adm maxPQ.
set R := ~: right_image (right_image Q); set C := ~: left_image (left_image P).
have [R' [C' prR]] := pruning R C.
have : objective R' C' <= objective P Q := maxPQ (R', C') (pruning_admissible adm prR).
rewrite /objective.
case: prR => /andP[RR CC] _ _ _ del.
have [gP gQ] := admissible_growth G0 pos sg adm.
have /andP[cf _] := adm; rewrite conflict_free_disjoint -setI_eq0 in cf.
have := cardsUI (left_image P) (right_image Q); rewrite (eqP cf) cards0 addn0.
have := cardsC (left_image P :|: right_image Q).
have := cardsC (right_image (right_image Q)); have := cardsC (left_image (left_image P)).
have := subset_leq_card (Hset_uncovered P Q).
have := cardsID R' R; have := cardsID C' C.
rewrite (setIidPr RR) (setIidPr CC) -/R -/C.
have : #|Zset R C :\: (left_image R' :|: right_image C')| <=
       #|~: (left_image R' :|: right_image C')|.
  by apply: subset_leq_card; rewrite setDE subsetIr.
lia.
Qed.

End Extremal.
