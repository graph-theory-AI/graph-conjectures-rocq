(** * Fractional vertex-arboricity 2 implies large induced forests in planar graphs

If 2b sets F_1, ..., F_2b inducing forests cover every vertex of G at least b times, then
counting the pairs (v, i) with v in F_i gives b |G| <= Σ_i |F_i| <= 2b max_i |F_i|.  Hence the
largest F_i induces a forest with at least |G|/2 vertices.

The implication is the edge e121 of relations.json in graph-conjectures.  It was formalized in
graph-theory-rocq (atlas/theories/conjectures/implications_A1.v). *)

From GraphTheory Require Import digraph sgraph.
From mathcomp Require Import boot.
From GC.chromatic.AX_planar_fractional_vertex_arboricity_2 Require Import
  main(AX_planar_fractional_vertex_arboricity_2).
From GC.topological.OPG_albertson_berman_planar_induced_forest_half Require Import
  main(OPG_albertson_berman_planar_induced_forest_half).

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Theorem
  AX_planar_fractional_vertex_arboricity_2_implies_OPG_albertson_berman_planar_induced_forest_half :
  AX_planar_fractional_vertex_arboricity_2 -> OPG_albertson_berman_planar_induced_forest_half.
Proof.
move=> H G /H [b [b0 [F [forF cov]]]].
have i0 : 'I_(2 * b) by exists 0; rewrite muln_gt0 b0.
have [i _ maxi] := arg_maxnP (fun j => #|F j|) (isT : predT i0).
exists (F i); split => //; rewrite -(leq_pmul2l b0) mulnA [b * 2]mulnC.
apply: (@leq_trans (\sum_j #|F j|)); last first.
  by rewrite -[2 * b in X in _ <= X]card_ord -sum_nat_const; apply: leq_sum => j _; apply: maxi.
apply: (@leq_trans (\sum_v #|[set j | v \in F j]|)).
  by rewrite mulnC -sum_nat_const; apply: leq_sum => v _; apply: cov.
have cnt v : #|[set j | v \in F j]| = \sum_j (if v \in F j then 1 else 0).
  by rewrite -sum1_card big_mkcond; apply: eq_bigr => j _; rewrite inE.
rewrite (eq_bigr _ (fun v _ => cnt v)) exchange_big; apply: leq_sum => j _.
by rewrite -sum1_card [leqRHS]big_mkcond.
Qed.

Check
  (AX_planar_fractional_vertex_arboricity_2_implies_OPG_albertson_berman_planar_induced_forest_half
  : GC.chromatic.AX_planar_fractional_vertex_arboricity_2.main.AX_planar_fractional_vertex_arboricity_2 ->
    GC.topological.OPG_albertson_berman_planar_induced_forest_half.main.OPG_albertson_berman_planar_induced_forest_half).
Print Assumptions
  AX_planar_fractional_vertex_arboricity_2_implies_OPG_albertson_berman_planar_induced_forest_half.
