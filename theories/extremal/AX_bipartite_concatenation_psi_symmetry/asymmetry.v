(** * ψ(5/7,2/7) >= 6/7 > ψ(2/7,5/7)

Lower bound ψ(5/7,2/7) >= 6/7.  Suppose that, for every vertex c of C, the set U(c) of the
vertices of A that are not at distance two from c has more than |A|/7 elements.  For a in U(c),
the sets N(a) ∩ B and N(c) ∩ B are disjoint, of sizes at least 5|B|/7 and 2|B|/7, so that they
partition B.  Hence N(c) ∩ B has size 2|B|/7 exactly, and is determined by any vertex a of U(c):
the sets U(c) and U(c') are disjoint whenever N(c) ∩ B and N(c') ∩ B are distinct.  If moreover c
and c' have a common neighbour b in B, then U(c) and U(c') are included in A \ N(b), which has
size at most 2|A|/7: a contradiction.  Thus the sets N(c) ∩ B, for c in C, form a partition of B
into parts of size 2|B|/7, which is impossible since 7 is odd.

Upper bound ψ(2/7,5/7) <= 5/6.  An explicit graph with |A| = 6 and |B| = |C| = 7, where each
vertex of C has a vertex of A that is not at distance two.

The proof comes from Graph-Theory-LLM-Proofs (attacks/1902.10878__01), with 23/28 as upper bound
and |A| = 28.  It was formalized in graph-theory-rocq
(extremal-graph-theory/theories/applications/psi_asymmetry), and is simplified here. *)

From GraphTheory Require Import preliminaries digraph sgraph dom.
From GC.GraphLib Require Import misc.
From GC.extremal.AX_bipartite_concatenation_psi_symmetry Require main.
From mathcomp Require Import boot order algebra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.Theory GRing.Theory Num.Theory.

Abbreviation second_neigh := main.second_neigh.
Abbreviation biconstrained := main.biconstrained.
Abbreviation psi_ge := main.psi_ge.

Abbreviation q27 := (2%:R / 7%:R : rat)%R.
Abbreviation q57 := (5%:R / 7%:R : rat)%R.
Abbreviation q67 := (6%:R / 7%:R : rat)%R.

(** Inequalities [p/7 * m <= n] in natural numbers. *)
Lemma ratio_le (p m n : nat) : (p%:R / 7%:R * m%:R <= n%:R :> rat)%R = (p * m <= 7 * n).
Proof. by rewrite mulrAC ler_pdivrMr // -!natrM ler_nat [n * 7]mulnC. Qed.

(** ** Lower bound *)

Section LowerBound.

Variables (G : sgraph) (A B C : {set G}).
Hypothesis bic : biconstrained q57 q27 A B C.

Lemma neigh_AB a : a \in A -> 5 * #|B| <= 7 * #|B :&: N(a)|.
Proof.
move=> aA; case/and5P: bic => _ _ /forall_inP/(_ a aA) + _ _.
by rewrite ratio_le setIC.
Qed.

Lemma neigh_BC b : b \in B -> 2 * #|C| <= 7 * #|N(b) :&: C|.
Proof.
by move=> bB; case/and5P: bic => _ _ _ /forall_inP/(_ b bB) + _; rewrite ratio_le.
Qed.

Lemma neigh_BA b : b \in B -> 5 * #|A| <= 7 * #|A :&: N(b)|.
Proof.
move=> bB; case/and5P: bic => _ _ _ _ /andP[/forall_inP/(_ b bB) + _].
by rewrite ratio_le setIC.
Qed.

Lemma neigh_CB c : c \in C -> 2 * #|B| <= 7 * #|N(c) :&: B|.
Proof.
by move=> cC; case/and5P: bic => _ _ _ _ /andP[_ /forall_inP/(_ c cC)]; rewrite ratio_le.
Qed.

Lemma B_C_neq0 : (0 < #|B|) && (0 < #|C|).
Proof.
case/and5P: bic => /and5P[_ _ _ _ /andP[/and3P[_ B0 C0] _]] _ _ _ _.
by rewrite !card_gt0 B0 C0.
Qed.

(** A set containing at least 5/7 of the elements misses at most 2/7 of them. *)
Lemma card_setD_le (S T : {set G}) : 5 * #|S| <= 7 * #|S :&: T| -> 7 * #|S :\: T| <= 2 * #|S|.
Proof.
move=> h; rewrite -(leq_add2l (5 * #|S|)) -mulnDl -[in leqRHS](cardsID T S) mulnDr.
by rewrite leq_add2r.
Qed.

(** If [a] is not at distance two from [c], then the neighbourhoods of [a] and [c] partition [B],
and [c] has 2/7 of the vertices of [B] as neighbours. *)
Lemma rigid a c : a \in A -> c \in C -> a \notin second_neigh c ->
  N(c) :&: B = B :\: N(a) /\ 7 * #|N(c) :&: B| = 2 * #|B|.
Proof.
move=> aA cC; have hc := neigh_CB cC; have ha := card_setD_le (neigh_AB aA).
case/and5P: bic => /and5P[_ _ _ dAC _] /forall_inP/(_ a aA)/forall_inP/(_ c cC) nac _ _ _.
have ac : a != c by apply: contraTneq aA => ->; rewrite (disjointFl dAC cC).
rewrite inE ac nac /= negbK => /eqP/setP cn.
have sub : N(c) :&: B \subset B :\: N(a).
  apply/subsetP => b; rewrite !inE => /andP[cb ->]; rewrite andbT.
  by apply/negP => ab; have := cn b; rewrite !inE ab cb.
have le := subset_leq_card sub.
split; last by apply/eqP; rewrite eqn_leq hc andbT (leq_trans _ ha) // leq_mul2l.
by apply/eqP; rewrite eqEcard sub -(leq_pmul2l (_ : 0 < 7)) // (leq_trans ha).
Qed.

(** Assume that, for each vertex of [C], more than 1/7 of the vertices of [A] are not at distance
two. *)
Let U (c : G) := A :\: second_neigh c.
Hypothesis big : forall c, c \in C -> #|A| < 7 * #|U c|.

Lemma U_neq0 c : c \in C -> exists2 a, a \in A & a \notin second_neigh c.
Proof.
move=> cC; have /card_gt0P[a] : 0 < #|U c|.
  by rewrite -(ltn_pmul2l (_ : 0 < 7)) // (leq_ltn_trans _ (big cC)).
by rewrite in_setD => /andP[]; exists a.
Qed.

(** The vertices of [U c] are not adjacent to the neighbours of [c] in [B]. *)
Lemma U_sub b c : c \in C -> b \in N(c) :&: B -> U c \subset A :\: N(b).
Proof.
move=> cC bc; apply/subsetP => a; rewrite !in_setD => /andP[na aA].
by move: bc; rewrite aA (rigid aA cC na).1 !inE sg_sym => /andP[->].
Qed.

(** Two vertices of [C] with a common neighbour in [B] have the same neighbours in [B]. *)
Lemma same_neigh b c c' : c \in C -> c' \in C -> b \in N(c) :&: B -> b \in N(c') :&: B ->
  N(c) :&: B = N(c') :&: B.
Proof.
move=> cC c'C bc bc'; apply/eqP/contraT => neq.
have dis : [disjoint U c & U c'].
  apply/pred0P => a /=; apply/negP => /andP[]; rewrite !in_setD => /andP[na aA] /andP[na' _].
  by case/eqP: neq; rewrite (rigid aA cC na).1 (rigid aA c'C na').1.
have bB : b \in B by move: bc; rewrite inE => /andP[].
have : #|U c| + #|U c'| <= #|A :\: N(b)|.
  by rewrite -cardsUI (disjoint_setI0 dis) cards0 addn0 subset_leq_card // subUset !U_sub.
rewrite -(leq_pmul2l (_ : 0 < 7)) // => /leq_trans/(_ (card_setD_le (neigh_BA bB))).
by rewrite mulnDr mul2n -addnn leqNgt (leq_trans _ (leq_add (big cC) (ltnW (big c'C)))).
Qed.

Lemma lower_bound_contra : False.
Proof.
have /andP[B0 /card_gt0P[c0 c0C]] := B_C_neq0.
pose n := #|N(c0) :&: B|.
have size_n c : c \in C -> 7 * #|N(c) :&: B| = 2 * #|B|.
  by move=> cC; have [a aA na] := U_neq0 cC; case: (rigid aA cC na).
pose P := [set N(c) :&: B | c in C].
have partP : partition P B.
  apply/and3P; split.
  - rewrite cover_imset; apply/eqP/setP => b; apply/bigcupP/idP => [[c _]|bB].
      by rewrite inE => /andP[].
    have /card_gt0P[c] : 0 < #|N(b) :&: C|.
      rewrite -(ltn_pmul2l (_ : 0 < 7)) // muln0 (leq_trans _ (neigh_BC bB)) // muln_gt0 /=.
      by apply/card_gt0P; exists c0.
    by rewrite !inE => /andP[bc cC]; exists c => //; rewrite !inE sg_sym bc.
  - apply/trivIsetP => _ _ /imsetP[c cC ->] /imsetP[c' c'C ->] neq.
    apply/pred0P => b /=; apply: contraNF neq => /andP[bc bc'].
    by rewrite (same_neigh cC c'C bc bc').
  - apply/imsetP => -[c cC /esym/eqP]; rewrite -cards_eq0 => /eqP e.
    by have := size_n c cC; rewrite e muln0 => /esym/eqP; rewrite muln_eq0 /= eqn0Ngt B0.
have cardP : {in P, forall S : {set G}, #|S| = n}.
  move=> _ /imsetP[c cC ->]; apply/eqP.
  by rewrite -(eqn_pmul2l (_ : 0 < 7)) // !size_n.
have := congr1 (muln 7) (card_uniform_partition cardP partP).
rewrite mulnCA size_n // mulnA => /eqP; rewrite eqn_pmul2r // => /eqP/(congr1 odd).
by rewrite muln2 odd_double.
Qed.

End LowerBound.

(** ψ(5/7,2/7) >= 6/7. *)
Lemma lower_bound : psi_ge q57 q27 q67.
Proof.
move=> G A B C bic; apply/exists_inP; apply/contraT => /exists_inPn none.
case: (lower_bound_contra bic) => c cC; have := none c cC; rewrite ratio_le -ltnNge => h.
rewrite -(ltn_add2l (6 * #|A|)) addnC -mulSn -{1}(cardsID (second_neigh c) A) mulnDr.
by rewrite ltn_add2r.
Qed.

(** ** Upper bound *)

(** The vertices are numbered from 0 to 19, with A = {0,...,5}, B = {6,...,12}, C = {13,...,19}.
The number of the part of a vertex: *)
Definition part (x : nat) : nat := if x < 6 then 0 else if x < 13 then 1 else 2.

(** The neighbours in B of the vertices of A (the first five sets are disjoint from the
neighbourhoods of some vertices of C, the last one is B). *)
Definition neighA : seq (seq nat) :=
  [:: [:: 6; 7]; [:: 8; 9]; [:: 10; 11]; [:: 10; 12]; [:: 11; 12]; iota 6 7].

(** For each vertex [c] of C, the vertex of A that is not at distance two from [c], of which the
neighbours in B are the non-neighbours of [c]. *)
Definition miss (c : nat) : nat := nth 0 [:: 0; 0; 1; 1; 2; 3; 4] (c - 13).

(** The edges from A to B and from B to C. *)
Definition nadj (x y : nat) : bool :=
  [&& part x == 0, part y == 1 & y \in nth [::] neighA x] ||
  [&& part x == 1, part y == 2 & x \notin nth [::] neighA (miss y)].

(** The graph, and the set of vertices of part [i]. *)
Definition H : sgraph := sgraph_of_rel (fun x y : 'I_20 => nadj x y).

Definition part_set (i : nat) : {set H} := [set x : 'I_20 | part x == i].

(** Edges join consecutive parts. *)
Lemma edge_part (x y : H) :
  x -- y -> part (val y) = (part (val x)).+1 \/ part (val x) = (part (val y)).+1.
Proof.
by case/andP=> _ /orP[]; case/orP; case/and3P=> /eqP-> /eqP-> _; [left|left|right|right].
Qed.

(** Cardinals are computed by enumerating the numbers of the vertices. *)
Lemma card_H (S : {set H}) (P : pred nat) :
  (forall x : 'I_20, (x \in S) = P x) -> #|S| = count P (iota 0 20).
Proof.
move=> SP; rewrite cardE /enum_mem size_filter -val_enum_ord count_map [enum 'I_20]enumT.
by apply: eq_count => x; rewrite /= SP.
Qed.

Lemma card_part (i : nat) : #|part_set i| = count (fun x => part x == i) (iota 0 20).
Proof. by apply: card_H => x; rewrite inE. Qed.

(** The number of neighbours of [x] in part [i]. *)
Definition deg (x i : nat) : nat :=
  count (fun y => (x != y) && sc nadj x y && (part y == i)) (iota 0 20).

(** Degree conditions, checked by computation. *)
Lemma deg_part (p i j : nat) :
  all (fun x => (part x == i) ==> (p * count (fun y => part y == j) (iota 0 20) <= 7 * deg x j))
    (iota 0 20) ->
  [forall x in part_set i, p%:R / 7%:R * #|part_set j|%:R <= #|N(x) :&: part_set j|%:R :> rat]%R.
Proof.
move=> /allP degP; apply/forall_inP => x; rewrite inE => xi; rewrite ratio_le.
have := degP (val x); rewrite mem_iota ltn_ord xi => /(_ isT).
have -> : deg (val x) j = #|N(x) :&: part_set j|.
  by apply/esym/card_H => y; rewrite !inE.
by rewrite -card_part.
Qed.

Lemma biconstrained_H : biconstrained q27 q57 (part_set 0) (part_set 1) (part_set 2).
Proof.
have dis i j : i != j -> [disjoint part_set i & part_set j].
  move=> ij; apply/pred0P => x /=; rewrite !inE.
  by apply: contraNF ij => /andP[/eqP <- /eqP <-].
have sta i : stable (part_set i).
  apply/stableP => x y; rewrite !inE => /eqP xi /eqP yi; apply/negP => /edge_part.
  by rewrite xi yi => -[|] /eqP; rewrite ltn_eqF.
apply/and5P; split; [apply/and5P; split|..|apply/andP; split]; try exact: dis.
- by apply/eqP/setP => x; rewrite !inE /part; case: ifP => // _; case: ifP.
- by rewrite !sta -!card_gt0 !card_part.
- apply/forall_inP => a; rewrite inE => /eqP a0; apply/forall_inP => c; rewrite inE => /eqP c2.
  by apply/negP => /edge_part; rewrite a0 c2 => -[].
all: by apply: deg_part; vm_compute.
Qed.

(** Each vertex of C has a vertex of A that is not at distance two. *)
Lemma miss_second_neigh (c : H) :
  c \in part_set 2 -> exists2 a, a \in part_set 0 & a \notin second_neigh c.
Proof.
rewrite inE => /eqP cC; have lt6 : miss (val c) < 6.
  by rewrite /miss; case: (val c - 13) => [|[|[|[|[|[|[|[|n]]]]]]]].
pose a : H := Ordinal (ltn_trans lt6 (isT : 6 < 20)); have a0 : part (val a) = 0.
  by rewrite /part lt6.
exists a; rewrite inE ?a0 // !negb_and 2!negbK; apply/orP; right; apply/orP; right.
rewrite -subset0; apply/subsetP => w; rewrite !inE => /andP[/andP[_ aw] /andP[_ cw]].
move: aw cw; rewrite /sc /= /nadj a0 cC !andbF !orbF /= => /andP[_ w_a] /andP[_ /negP].
by case.
Qed.

(** ψ(2/7,5/7) <= 5/6 < 6/7. *)
Lemma upper_bound : ~ psi_ge q27 q57 q67.
Proof.
move=> /(_ H _ _ _ biconstrained_H) [c /miss_second_neigh[a aA na]].
have card_A : #|part_set 0| = 6 := card_part 0.
suff : #|part_set 0 :&: second_neigh c| <= 5.
  by rewrite ratio_le card_A -(leq_pmul2l (_ : 0 < 7)) // => le5 /leq_trans/(_ le5).
rewrite -ltnS -[leqRHS]card_A; apply: proper_card; apply/properP; split; first exact: subsetIl.
by exists a => //; rewrite in_setI (negbTE na) andbF.
Qed.

(** ψ(5/7,2/7) and ψ(2/7,5/7) are distinct. *)
Theorem psi_asymmetry : ~ main.AX_bipartite_concatenation_psi_symmetry.
Proof.
move=> sym; apply: upper_bound; apply/(sym q57 q27 q67) => //; exact: lower_bound.
Qed.
