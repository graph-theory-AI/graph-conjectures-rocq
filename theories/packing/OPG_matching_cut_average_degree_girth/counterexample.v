(** * Graphs of large girth and bounded degree without matching cut

Main file of the disproof: for d = 35 and all g, there is a graph of average degree smaller than d
and girth at least g without matching cut.  It is built by the greedy construction of greedy.v,
with 17 edges from each vertex.  If the edges between a set A of a <= n/2 vertices and its
complement form a matching, then at most a of the 17a edges from A leave A, and the term of A in
the final potential is at least 1, up to normalisation [weight_small].  But the initial potential
is less than 1 (initial_potential.v), and the construction does not increase it.

The existence of such graphs, with maximum degree at most 60, also follows from the proof by
Feghali, Lucke, Paulusma and Ries (arXiv:2212.12317) that recognizing the graphs with a matching
cut is NP-complete for these girths and degrees.  The proof given here is different. *)

From GraphTheory Require Import digraph sgraph.
From GC.packing.OPG_matching_cut_average_degree_girth Require main.
From GC.packing.OPG_matching_cut_average_degree_girth Require Import greedy initial_potential.
From mathcomp Require Import boot zify.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Graph.
Variables (d n g : nat) (E : seq ('I_n * 'I_n)).
Hypothesis goodE : good d.+2 g E.
Hypothesis outE : perm_eq (unzip1 E) (sources d n).

Lemma adj_sym : symmetric (adj E). Proof. by move=> x y; exact: adjC. Qed.

Lemma adj_irrefl : irreflexive (adj E).
Proof. by case: goodE => _ _ lE _ x; exact/negbTE/lE. Qed.

Definition sparse_graph : sgraph := SGraph adj_sym adj_irrefl.

Lemma outdegE x : outdeg E x = d.+2.
Proof. by rewrite /outdeg (permP outE) count_mem_sources. Qed.

Lemma sparse_graph_girth : main.girth_ge sparse_graph g.
Proof. by case: goodE => gE _ _ _ c /andP[cc c2]; exact: gE. Qed.

Lemma sum_degrees : \sum_(v : sparse_graph) #|N(v)| <= 2 * d.+2 * n.
Proof.
have sumE : \sum_x outdeg E x = d.+2 * n.
  by under eq_bigr do rewrite outdegE; rewrite sum_nat_const card_ord mulnC.
apply: (@leq_trans (\sum_(x < n) (outdeg E x + indeg E x))).
  by apply: leq_sum => x _; rewrite (leq_trans _ (card_adj E x)) // cardsE.
rewrite big_split /= sumE sum_count size_map -[size E](size_map Datatypes.fst) -sum_count sumE.
lia.
Qed.

(** If at most one edge from each vertex of [A] leaves [A], then at most [#|A|] of the
    [d.+2 * #|A|] edges from [A] leave [A]. *)
Lemma weight_small (A : {set 'I_n}) : 2 * #|A| <= n ->
    (forall x, x \in A -> #|[set y | adj E x y] :\: A| <= 1) ->
  threshold d n #|A| <= \prod_(e <- E) weight A e.
Proof.
move=> An cutA; case: goodE => _ uE _ _.
pose inner e := (e.1 \in A) && (e.2 \in A); pose outer e := (e.1 \in A) && (e.2 \notin A).
have -> : \prod_(e <- E) weight A e = (4 * n) ^ count inner E * #|A| ^ count outer E.
  elim: (E) => [|e s IH]; first by rewrite big_nil.
  rewrite big_cons IH /weight /= /inner /outer !expnD.
  case: (e.1 \in A); case: (e.2 \in A); rewrite /= ?mul1n ?expn1 ?mulnA //.
  by rewrite -!mulnA mulnCA.
have outer_le : count outer E <= #|A|.
  rewrite -size_filter -(size_map Datatypes.fst) cardE uniq_leq_size //.
    rewrite map_inj_in_uniq ?filter_uniq // => -[x y] [x' y']; rewrite !mem_filter /=.
    move=> /andP[/andP[/= xA yA] xy] /andP[/andP[/= _ y'A] xy'] xx'; rewrite -xx' in xy' *.
    congr (_, _); have /card_le1_eqP := cutA x xA; apply; rewrite !inE.
      by apply/andP; split=> //; apply/orP; left.
    by apply/andP; split=> //; apply/orP; left.
  by move=> x /mapP[e]; rewrite mem_filter mem_enum => /andP[/andP[eA _] _] ->.
have allE : count inner E + count outer E = d.+2 * #|A|.
  rewrite -count_sources -(permP outE) count_map.
  elim: (E) => //= e s <-; rewrite addnACA /inner /outer.
  by case: (e.1 \in A); case: (e.2 \in A).
have -> : count inner E = d.+1 * #|A| + (#|A| - count outer E) by lia.
rewrite expnD -mulnA leq_mul2l; apply/orP; right.
rewrite -[X in _ ^ X <= _](subnK outer_le) expnD leq_mul2r; apply/orP; right.
by case: (_ - _) => // k; rewrite leq_exp2r //; lia.
Qed.

End Graph.

Lemma counterexample : ~ main.OPG_matching_cut_average_degree_girth.
Proof.
have [d large_d] : exists d, 6 ^ d.+2 * 8 <= 4 ^ d.+1 * 2 ^ d by exists 15; lia.
move=> /(_ (2 * d.+2).+1)[g0]; set g := g0.+2; pose n := 10 * ball_size d.+2 g.
have n1 : 1 < n by rewrite /n; have : 0 < ball_size d.+2 g by []; lia.
have good0 : @good d.+2 n g [::].
  by split=> // -[|x [|y c]] //= /andP[/andP[]].
have [|||x|E [goodE eE lePhi]] :=
  @extend d.+2 n (coeff d n) g [::] (sources d n) _ _ _ good0 => //.
  by rewrite addn0 count_mem_sources.
rewrite cats0 in eE; have outE : perm_eq (unzip1 E) (sources d n).
  by rewrite eE perm_rev.
have := leq_ltn_trans lePhi (initial_potential large_d n); rewrite ltnNge => /negP ltPhi.
have potential_ge (A : {set 'I_n}) : small A ->
    (forall x, x \in A -> #|[set y | adj E x y] :\: A| <= 1) -> False.
  move=> sA cutA; apply: ltPhi; rewrite /potential (bigD1 A) //=.
  apply: leq_trans (leq_addr _ _); rewrite mul1n; case/andP: sA => A0 An.
  rewrite -(@coeffE d n #|A|); first by rewrite A0 (leq_trans _ An) ?leq_pmull.
  by rewrite leq_mul2l (weight_small goodE outE) ?orbT.
move=> /(_ (sparse_graph goodE)); rewrite card_ord => /(_ n1) [||A [A0 AT cutA]].
- by apply: leq_ltn_trans (sum_degrees goodE outE) _; lia.
- by move=> c cc; apply: leq_trans (sparse_graph_girth cc); rewrite /g; lia.
have : (2 * #|A| <= n) || (2 * #|~: A| <= n) by have := cardsC A; rewrite card_ord; lia.
have crossing (B : {set 'I_n}) x :
    [set y | adj E x y] :\: B = N(x : sparse_graph goodE) :&: ~: B.
  by rewrite setDE; congr (_ :&: _); apply/setP => y; rewrite !inE.
case/orP => small_A.
  apply: (potential_ge A) => [|x xA]; first by rewrite /small card_gt0 A0.
  by rewrite crossing; have [/(_ xA)] := cutA x.
apply: (potential_ge (~: A)) => [|x xA]; last first.
  by rewrite crossing setCK; have [_] := cutA x; apply; rewrite inE in xA.
rewrite /small small_A card_gt0 andbT; apply: contraNneq AT => cA.
by rewrite -[A]setCK cA setC0.
Qed.
