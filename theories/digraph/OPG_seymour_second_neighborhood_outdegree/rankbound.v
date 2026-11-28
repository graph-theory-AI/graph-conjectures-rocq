(** * The matching bound of the pruning lemma

If O is a matching of conflicts between R and C, alpha and beta are matchings of [alpha_rel]
and [beta_rel], and the members matched by O are not matched by alpha and beta, then
|O| + |alpha| + |beta| <= |Z| + |H|.  In other words, every matching of the augmented graph of
the pruning lemma has at most |Z| + |H| edges.

Proof.  Take the coefficients of [exists_coefficients], and put X = (L | -B) (of size
|R| x (|Z| + |H|)) and Y = (N over A) (of size (|Z| + |H|) x |C|).  Then X Y = L N - B A = 0 by
[maps_commute], so rank X + rank N <= rank X + rank Y <= |Z| + |H|.  Split O: O2 is the set of
edges (r,c) such that every vector v of the kernel of the transpose of N vanishes at c, O1 the
others.
- The rows of X indexed by the members of R matched by alpha or by O1 are independent: a
  vanishing combination u satisfies u B = 0, hence u_r = 0 at the left end r of each edge
  (r,c) of O1 ([conflict_kernel] with a vector v such that v_c <> 0); then u L = 0 and u is
  supported on the rows of alpha, so u = 0.  Hence rank X >= |alpha| + |O1|.
- The rows of the transpose of N indexed by the members of C matched by beta or by O2 are
  independent: a vanishing combination v vanishes on O2 by definition, then on the rows of
  beta.  Hence rank N >= |beta| + |O2|.
This argument needs no maximum matching: unlike the paper and its Lean formalization, it only
uses lower bounds on the ranks of L and N, and no kernel lifts.

Provenance: this follows Section 3 of the paper "A proof of Seymour's second-neighborhood
conjecture" of OpenAI, a model-generated manuscript that is not peer reviewed,
https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/preprints/A-proof-of-Seymours-second-neighborhood-conjecture-September-23-2026/paper.pdf
and its Lean formalization (KernelBasisLifts.lean, KernelIndependence.lean,
CompositeRankBound.lean, RankBoundFromMinors.lean, AugmentedRankBound.lean),
https://github.com/openai/math/tree/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Combinatorics/SecondNeighborhood
which proves the full statement of the conjecture.  The rank argument above is a
simplification of theirs. *)

From GraphTheory Require Import digraph.
From GC.GraphLib Require Import konig linear_algebra.
From GC.digraph.OPG_seymour_second_neighborhood_outdegree Require Import
  defs mxmaps coeffs.
From mathcomp Require Import boot order algebra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** If the rows [S] of [M] are independent and every left kernel vector of [M'] is a left kernel
    vector of [M] vanishing on [T], then the rows [S :|: T] of [M'] are independent. *)
Local Lemma free_rows_add m n p (M : 'M[rat]_(m, n)) (M' : 'M[rat]_(m, p)) (S T : {set 'I_m}) :
  free_rows M S ->
  (forall u : 'rV_m, u *m M' = 0 -> u *m M = 0 /\ {in T, forall i, u 0 i = 0}) ->
  free_rows M' (S :|: T).
Proof.
move=> fM h u uST /h [uM uT]; apply: fM uM => i iS.
by have [/uT //|iT] := boolP (i \in T); apply: uST; rewrite inE negb_or iS iT.
Qed.

Local Lemma cardsU_disjoint (T : finType) (A B : {set T}) :
  A :&: B = set0 -> #|A :|: B| = (#|A| + #|B|)%N.
Proof. by move=> AB; rewrite -cardsUI AB cards0 addn0. Qed.

Section RankBound.
Variables (G : diGraph) (R C : {set G * G}).

Theorem corner_bound (O alpha beta : {set (G * G) * (G * G)}) :
  bimatching (orig_rel R C) O ->
  bimatching (alpha_rel R C) alpha -> bimatching (beta_rel R C) beta ->
  {in O & alpha, forall e f, e.1 != f.2} -> {in O & beta, forall e f, e.2 != f.2} ->
  (#|O| + #|alpha| + #|beta| <= #|Zset R C| + #|Hset R C|)%N.
Proof.
move=> /bimatchingP [Orel Oinj1 Oinj2] mal mbe Oal Obe.
have [a [b [fL fN lmr]]] := exists_coefficients mal mbe.
set L := L_mx R C a; set N := N_mx R C b; set B := B_mx R C b.
pose X := row_mx L (- B); pose Y := col_mx N (A_mx R C a).
have XY : X *m Y = 0 by rewrite mul_row_col mulNmx -maps_commute addrN.
pose K := kermx N^T.
have KN v : (v <= K)%MS -> N *m v^T = 0.
  by move=> /sub_kermxP vN; rewrite -[N]trmxK -trmx_mul vN trmx0.
(* O1: the edges (r, c) of O such that some kernel vector of N^T does not vanish at c. *)
pose P : {set (G * G) * (G * G)} :=
  [set e | [exists c : 'I_#|C|, (idx c == e.2) && (col c K != 0)]].
pose O1 := O :&: P; pose O2 := O :\: P.
pose T1 := [set r : 'I_#|R| | idx r \in [set e.1 | e in O1]].
pose T2 := [set c : 'I_#|C| | idx c \in [set e.2 | e in O2]].
have Ofst e : e \in O -> e.1 \in R by move=> /Orel /and3P [].
have Osnd e : e \in O -> e.2 \in C by move=> /Orel /and3P [].
have cardT1 : #|T1| = #|O1|.
  by apply: card_idx_imset => [e f /setIP[eO _] /setIP[fO _]|e /setIP[/Ofst ? _]] //; apply: Oinj1.
have cardT2 : #|T2| = #|O2|.
  by apply: card_idx_imset => [e f /setDP[eO _] /setDP[fO _]|e /setDP[/Osnd ? _]] //; apply: Oinj2.
(* The rows of X of the members matched by alpha and of the left ends of O1 are free. *)
have fX : free_rows X (alpha_rows R alpha :|: T1).
  apply: free_rows_add fL _ => u; rewrite mul_mx_row -row_mx0 => /eq_row_mx [uL].
  move/eqP; rewrite mulmxN oppr_eq0 => /eqP uB; split=> // r.
  rewrite inE => /imsetP [e /setIP [eO]]; rewrite inE => /existsP [c /andP [/eqP ce Kc]] re.
  have /existsP [k Kkc] : [exists k, K k c != 0].
    apply: contraR Kc => /existsPn h; apply/eqP/matrixP => k j.
    by rewrite [LHS]mxE [RHS]mxE; apply/eqP; rewrite -[_ == _]negbK; exact: h.
  have rc : conflict (idx r) (idx c) by rewrite re ce; case/and3P: (Orel _ eO).
  move: (conflict_kernel lmr uB (KN _ _ (row_sub k K)) rc) => /eqP.
  by rewrite [row _ _ _ _]mxE mulf_eq0 (negbTE Kkc) orbF => /eqP.
(* The rows of N^T of the members matched by beta and of the right ends of O2 are free. *)
have fNT : free_rows N^T (beta_rows C beta :|: T2).
  apply: free_rows_add fN _ => v vN; split=> // c.
  rewrite inE => /imsetP [e /setDP [eO]]; rewrite inE negb_exists => /forallP /(_ c) eP ce.
  move: eP; rewrite ce eqxx negbK => /eqP Kc0.
  have /submxP [w vK] : (v <= K)%MS by apply/sub_kermxP.
  have /matrixP /(_ 0 0) : col c v = 0 by rewrite colE vK -mulmxA -colE Kc0 mulmx0.
  by rewrite !mxE.
have rN : (\rank N <= \rank Y)%N by apply: mxrankS; rewrite -addsmxE addsmxSl.
have dis1 : alpha_rows R alpha :&: T1 = set0.
  apply/setP => r; rewrite !inE.
  apply/andP => -[/imsetP [f fal fr] /imsetP [e /setIP [eO _] er]].
  by move: (Oal _ _ eO fal); rewrite -er fr eqxx.
have dis2 : beta_rows C beta :&: T2 = set0.
  apply/setP => c; rewrite !inE.
  apply/andP => -[/imsetP [f fbe fc] /imsetP [e /setDP [eO _] ec]].
  by move: (Obe _ _ eO fbe); rewrite -ec fc eqxx.
move: (free_rows_rank fX) (free_rows_rank fNT) (mulmx0_rank_max XY); rewrite mxrank_tr.
rewrite !cardsU_disjoint // (card_alpha_rows mal) (card_beta_rows mbe) cardT1 cardT2.
rewrite -(cardsID P O) -/O1 -/O2 => h1 h2 h3.
rewrite -addnA addnACA (addnC #|O1|) (addnC #|O2|).
exact: leq_trans (leq_add h1 (leq_trans h2 rN)) h3.
Qed.

End RankBound.
