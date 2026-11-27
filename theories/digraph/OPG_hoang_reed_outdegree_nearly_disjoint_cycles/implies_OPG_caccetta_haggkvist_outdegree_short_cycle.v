(** * The Hoàng-Reed conjecture implies the Caccetta-Häggkvist conjecture

Let D be a digraph with n vertices and minimum out-degree at least r.  It has r directed cycles
such that each of them meets the union of the previous ones in at most one vertex.  The first cycle
has no previous cycle, hence the sum of the numbers of vertices of the cycles is at most n + r - 1,
and the shortest cycle has at most ⌈n/r⌉ vertices.

The implication is mentioned in the Open Problem Garden, and is the edge e172 of relations.json in
graph-conjectures.  It was formalized in graph-theory-rocq
(digraph-theory/theories/conjectures/implications_P9.v). *)

From GraphTheory Require Import digraph.
From mathcomp Require Import boot.
From GC.digraph.OPG_hoang_reed_outdegree_nearly_disjoint_cycles Require Import
  main(OPG_hoang_reed_outdegree_nearly_disjoint_cycles).
From GC.digraph.OPG_caccetta_haggkvist_outdegree_short_cycle Require Import
  main(OPG_caccetta_haggkvist_outdegree_short_cycle).

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** If each of [r.+1] sets meets the union of the previous ones in at most one element, then the sum
    of their cardinals is at most [#|T| + r]. *)
Lemma sum_nearly_disjoint (T : finType) (r : nat) (C : 'I_r.+1 -> {set T}) :
  (forall j, #|[set v in C j | [exists i : 'I_r.+1, (i < j) && (v \in C i)]]| <= 1) ->
  \sum_j #|C j| <= #|T| + r.
Proof.
move=> old1; pose old j := [set v in C j | [exists i : 'I_r.+1, (i < j) && (v \in C i)]].
rewrite (eq_bigr (fun j => #|C j :\: old j| + #|C j :&: old j|)) => [j _|]; last first.
  rewrite big_split leq_add //=.
    rewrite (eq_bigr (fun j => \sum_(v in C j :\: old j) 1)) => [j _|]; first by rewrite sum1_card.
    rewrite -partition_disjoint_bigcup ?sum1_card ?max_card // => i j.
    wlog ij : i j / i < j => [hw|_].
      by rewrite neq_ltn => /orP[ij|ji]; [|rewrite disjoint_sym]; apply: hw => //;
         rewrite neq_ltn ?ij ?ji ?orbT.
    rewrite -setI_eq0; apply/eqP/setP => v; rewrite !inE.
    apply/negP => /andP[/andP[_ vi] /andP[/negP vold vj]]; apply: vold.
    by rewrite vj; apply/existsP; exists i; rewrite ij.
  rewrite big_ord_recl (_ : _ :&: _ = set0) ?cards0.
    by apply/setP => v; rewrite !inE; apply/negP => /and3P[_ _ /existsP[]].
  rewrite add0n -[X in _ <= X]card_ord -sum1_card; apply: leq_sum => j _.
  exact: leq_trans (subset_leq_card (subsetIr _ _)) (old1 _).
by rewrite addnC cardsID.
Qed.

Theorem OPG_hoang_reed_outdegree_nearly_disjoint_cycles_implies_OPG_caccetta_haggkvist_outdegree_short_cycle :
  OPG_hoang_reed_outdegree_nearly_disjoint_cycles -> OPG_caccetta_haggkvist_outdegree_short_cycle.
Proof.
move=> HR D [//|r] D_gt0 _ _ deg; have [C [cycC metC]] := HR D r.+1 D_gt0 deg.
have sizeC j : #|[set v in C j]| = size (C j).
  by rewrite cardsE; apply/card_uniqP; case/and3P: (cycC j).
have [/existsP[j short]|/existsPn long] :=
  boolP [exists j, size (C j) <= (#|D| + r.+1 - 1) %/ r.+1]; first by exists (C j).
have : \sum_j #|[set v in C j]| <= #|D| + r.
  apply: sum_nearly_disjoint => j; apply: leq_trans (metC j); apply/eq_leq/eq_card => v.
  by rewrite !inE; congr (_ && _); apply: eq_existsb => i; rewrite inE.
rewrite leqNgt => /negP[]; rewrite addnS subn1 /= in long.
apply: leq_trans (ltn_ceil (#|D| + r) (ltn0Sn r)) _; rewrite mulnC.
apply: (@leq_trans (\sum_(j < r.+1) ((#|D| + r) %/ r.+1).+1)).
  by rewrite sum_nat_const card_ord.
by apply: leq_sum => j _; rewrite sizeC ltnNge long.
Qed.

Check (OPG_hoang_reed_outdegree_nearly_disjoint_cycles_implies_OPG_caccetta_haggkvist_outdegree_short_cycle :
  GC.digraph.OPG_hoang_reed_outdegree_nearly_disjoint_cycles.main.OPG_hoang_reed_outdegree_nearly_disjoint_cycles ->
  GC.digraph.OPG_caccetta_haggkvist_outdegree_short_cycle.main.OPG_caccetta_haggkvist_outdegree_short_cycle).
Print Assumptions OPG_hoang_reed_outdegree_nearly_disjoint_cycles_implies_OPG_caccetta_haggkvist_outdegree_short_cycle.
