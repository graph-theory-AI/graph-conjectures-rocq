(** * Ramsey-nice for all large k implies Ramsey-nice for infinitely many k

If a family containing a forest is k-nice for every k >= k1, then, for every k0, it is k-nice for
k = max(k0, k1) >= k0.

The implication is the edge e160 of relations.json in graph-conjectures (Question 1.1 and
Conjecture 1.5 of arXiv:1708.07369).  It was formalized in graph-theory-rocq
(extremal-graph-theory/theories/conjectures/implications_X223.v). *)

From mathcomp Require Import boot.
From GC.extremal.AX_ramsey_nice_forest_families_eventually Require Import
  main(AX_ramsey_nice_forest_families_eventually).
From GC.extremal.AX_ramsey_nice_forest_families_infinitely_often Require Import
  main(AX_ramsey_nice_forest_families_infinitely_often).

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Theorem AX_ramsey_nice_forest_families_eventually_implies_AX_ramsey_nice_forest_families_infinitely_often :
  AX_ramsey_nice_forest_families_eventually -> AX_ramsey_nice_forest_families_infinitely_often.
Proof.
move=> H r Fam forest k0; have [k1 nice] := H r Fam forest.
by exists (maxn k0 k1); rewrite leq_maxl; split=> //; apply: nice; rewrite leq_maxr.
Qed.

Check (AX_ramsey_nice_forest_families_eventually_implies_AX_ramsey_nice_forest_families_infinitely_often :
  GC.extremal.AX_ramsey_nice_forest_families_eventually.main.AX_ramsey_nice_forest_families_eventually ->
  GC.extremal.AX_ramsey_nice_forest_families_infinitely_often.main.AX_ramsey_nice_forest_families_infinitely_often).
Print Assumptions AX_ramsey_nice_forest_families_eventually_implies_AX_ramsey_nice_forest_families_infinitely_often.
