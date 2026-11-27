(** * Sparse pairs in sparse H-free graphs give anticomplete pairs with one linear side

Conjecture 3.4 of Chudnovsky, Fox, Scott, Seymour and Spirkl implies their Conjecture 1.4.  Let
ε = p/d and s be given by Conjecture 3.4 for H, let K = 2d4^s and D = K + s + 2: the graphs G
with n > 1 vertices that are H-free and 1/D-bounded have an anticomplete pair (A', B') with
|A'| >= n^(1/D)/D and |B'| >= n/D.  If n <= D^D, take a vertex v and the set of its non-neighbours.
Otherwise let t be the integer D-th root of n, so that t >= D.  As G is ε-bounded, Conjecture 3.4
for c = 1/(4t) gives a c-sparse pair (A, B) with |A| >= 2t, since K t^(s+1) <= t^D <= n, and
|B| >= n/d.  At least half of the vertices of A have at most |B|/(2t) neighbours in B; t of them
have at most |B|/2 neighbours in B in all, and they are anticomplete to the other vertices of B.

The implication is the edge e077 of relations.json in graph-conjectures (the argument is that of
arXiv:1810.00058).  It was formalized in graph-theory-rocq
(extremal-graph-theory/theories/conjectures/implications_X223.v). *)

From GraphTheory Require Import digraph sgraph.
From mathcomp Require Import boot.
From GC.GraphLib Require Import misc.
From GC.extremal.AX_sparse_h_free_c_sparse_pairs Require Import
  main(AX_sparse_h_free_c_sparse_pairs).
From GC.extremal.AX_sparse_h_free_anticomplete_pairs_linear Require Import
  main(AX_sparse_h_free_anticomplete_pairs_linear).

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** The number of edges between [A] and [B] is the sum of the degrees in [B] of the vertices of
    [A]. *)
Lemma edge_count_betweenE (G : sgraph) (A B : {set G}) :
  edge_count_between A B = \sum_(a in A) #|N(a) :&: B|.
Proof.
rewrite /edge_count_between -sum1_card.
under [RHS]eq_bigr do rewrite -sum1_card.
rewrite pair_big_dep /=; apply: eq_bigl => -[a b] /=.
by rewrite !inE [_ -- _ && _]andbC.
Qed.

(** If [4t e(A, B) <= |A||B|], then [t] vertices of [A] are anticomplete to half of [B]. *)
Lemma sparse_anticomplete (G : sgraph) (A B : {set G}) (t : nat) :
  [disjoint A & B] -> 0 < t -> 2 * t <= #|A| -> 0 < #|B| ->
  4 * t * edge_count_between A B <= #|A| * #|B| ->
  exists A' B' : {set G}, [/\ anticomplete A' B', #|A'| = t & #|B| <= 2 * #|B'|].
Proof.
move=> dAB t0 tA B0 sp.
pose L := [set a in A | 2 * t * #|N(a) :&: B| <= #|B|].
have LA : L \subset A by apply/subsetP => a; rewrite inE => /andP[].
have AL : #|A| <= 2 * #|L|.
  have : 2 * #|A :\: L| * #|B| <= #|A| * #|B|.
    apply: leq_trans sp; rewrite edge_count_betweenE big_distrr /= (mulnC 2) -mulnA.
    rewrite -sum_nat_const [X in _ <= X](big_setID L) /=; apply: leq_trans (leq_addl _ _).
    apply: leq_sum => a; rewrite !inE => /andP[aL aA]; move: aL; rewrite aA -ltnNge => aL.
    by rewrite -(mulnA 4) -[4]/(2 * 2) -mulnA leq_mul2l mulnA ltnW.
  rewrite leq_pmul2r // -(cardsID L A) (setIidPr LA).
  by rewrite !mul2n -!addnn leq_add2r leq_add2l.
have [S SL cS] : exists2 S : {set G}, S \subset L & #|S| = t.
  have /card_geqP[s [us <- sL]] : t <= #|L| by rewrite -(leq_pmul2l (isT : 0 < 2)) (leq_trans tA).
  by exists [set x in s]; [apply/subsetP => x; rewrite inE => /sL | rewrite cardsE (card_uniqP us)].
pose U := \bigcup_(a in S) (N(a) :&: B).
have UB : U \subset B by apply/bigcupsP => a _; exact: subsetIr.
have hU : 2 * #|U| <= #|B|.
  apply: leq_trans (_ : 2 * \sum_(a in S) #|N(a) :&: B| <= _).
    rewrite leq_mul2l /U; apply/orP; right.
    elim/big_rec2: _ => [|a n V _ h]; first by rewrite cards0.
    by rewrite (leq_trans (leq_card_setU _ _).1) ?leq_add2l.
  rewrite -(leq_pmul2l t0) mulnCA mulnA big_distrr /= -{2}cS -sum_nat_const.
  by apply: leq_sum => a /(subsetP SL); rewrite inE => /andP[].
exists S, (B :\: U); split=> //.
  apply/andP; split.
    by apply: disjointWl (subset_trans SL LA) (disjointWr (subsetDl B U) dAB).
  apply/negP => /neighborP[a [b [aS]]]; rewrite inE => /andP[/negP bU bB] ab.
  by apply: bU; apply/bigcupP; exists a; rewrite // inE in_opn ab.
move: hU; rewrite -(cardsID U B) (setIidPr UB).
by rewrite !mul2n -!addnn leq_add2l leq_add2r.
Qed.

Theorem AX_sparse_h_free_c_sparse_pairs_implies_AX_sparse_h_free_anticomplete_pairs_linear :
  AX_sparse_h_free_c_sparse_pairs -> AX_sparse_h_free_anticomplete_pairs_linear.
Proof.
move=> HS H; have [p [d [s [p0 pd _ HG]]]] := HS H.
pose K := 2 * d * 4 ^ s; pose D := s.+1 + K.+1.
have KD : K <= D by rewrite /D addnS ltnW // ltnS leq_addl.
have dK : 2 * d <= K by rewrite /K leq_pmulr // expn_gt0.
have D2 : 2 <= D by rewrite /D addSn ltnS addnS ltnS.
exists 1, D; split=> // G G1 free bnd.
rewrite /main.eps_bounded mul1n in bnd.
set n := #|G| in G1 bnd *.
have n0 : 0 < n by apply: ltnW.
have d0 : 0 < d by apply: leq_trans pd.
have bnd' (v : G) : d * #|N[v]| < p * n.
  apply: leq_ltn_trans (leq_trans (bnd v) (leq_pmull _ p0)).
  by rewrite leq_mul2r (leq_trans (leq_pmull d (isT : 0 < 2))) ?(leq_trans dK KD) ?orbT.
case: (leqP n (D ^ D)) => [small|large].
  have /card_gt0P[v _] := n0.
  exists [set v], (~: N[v]); split.
  - apply/andP; split; first by rewrite disjoints1 inE v_in_clneigh.
    apply/negP => /neighborP[a [b]]; rewrite !inE.
    by case=> /eqP-> /norP[_ /negP].
  - by rewrite exp1n mul1n expn1 cards1 exp1n muln1.
  have : n + n < n + D * #|~: N[v]|.
    apply: leq_ltn_trans (_ : n + n <= D * n) _.
      by rewrite addnn -mul2n leq_mul2r D2 orbT.
    by rewrite {1}/n -(cardsC N[v]) mulnDr ltn_add2r.
  by rewrite ltn_add2l mul1n => /ltnW.
have D0 : 0 < D by apply: ltnW.
have [t tn tmax] : exists2 t, t ^ D <= n & n < t.+1 ^ D.
  have ex : exists t, t ^ D <= n by exists 0; rewrite exp0n.
  have ub t : t ^ D <= n -> t <= n.
    by case: t => // t; apply: leq_trans; rewrite -{1}(expn1 t.+1) leq_pexp2l.
  have [t tn tmax] := ex_maxnP ex ub.
  by exists t => //; rewrite ltnNge; apply/negP => /tmax; rewrite ltnn.
have Dt : D <= t by rewrite -ltnS -(ltn_exp2r _ _ D0); exact: ltn_trans large tmax.
have t0 : 0 < t by apply: leq_trans Dt.
have t4 : 0 < 4 * t by rewrite muln_gt0.
have [A [B [[dAB sp] hA hB]]] := HG G G1 free bnd' 1 (4 * t) t4 t4.
have tA : 2 * t <= #|A|.
  have : d * ((4 * t) ^ s * (2 * t)) <= d * ((4 * t) ^ s * #|A|).
    apply: leq_trans hA; rewrite exp1n mul1n; apply: leq_trans (leq_pmull _ p0).
    apply: leq_trans tn; rewrite /D expnD -[K.+1]addn1 expnD expn1.
    have -> : d * ((4 * t) ^ s * (2 * t)) = t ^ s.+1 * K.
      by rewrite /K expnMn expnSr (AC (1*(2*2)) ((3*5)*((4*1)*2))).
    by rewrite leq_mul2l (leq_trans (leq_trans KD Dt)) ?orbT // leq_pmull // expn_gt0 t0.
  by rewrite !leq_pmul2l // expn_gt0 muln_gt0 t0.
have B0 : 0 < #|B|.
  by move: hB; rewrite -(ltn_pmul2l d0) muln0; apply: leq_trans; rewrite muln_gt0 p0.
rewrite mul1n in sp; have [A' [B' [ac cA' hB']]] := sparse_anticomplete dAB t0 tA B0 sp.
exists A', B'; split=> //.
  rewrite exp1n mul1n expn1 cA' -expnMn; apply: ltnW (leq_trans tmax _).
  rewrite leq_exp2r // (@leq_trans (2 * t)) ?leq_mul2r ?D2 ?orbT //.
  by rewrite mul2n -addnn -addn1 leq_add2l.
rewrite mul1n; apply: leq_trans (leq_pmull _ p0) _; apply: leq_trans hB _.
apply: leq_trans (leq_mul (leqnn d) hB') _.
by rewrite mulnCA mulnA leq_mul2r (leq_trans dK KD) orbT.
Qed.

Check (AX_sparse_h_free_c_sparse_pairs_implies_AX_sparse_h_free_anticomplete_pairs_linear :
  GC.extremal.AX_sparse_h_free_c_sparse_pairs.main.AX_sparse_h_free_c_sparse_pairs ->
  GC.extremal.AX_sparse_h_free_anticomplete_pairs_linear.main.AX_sparse_h_free_anticomplete_pairs_linear).
Print Assumptions AX_sparse_h_free_c_sparse_pairs_implies_AX_sparse_h_free_anticomplete_pairs_linear.
