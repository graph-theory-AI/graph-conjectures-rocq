(** * Polynomial bound by the induced biclique number implies the bound for K_t,t-free graphs

If G has no induced K_t,t, its induced biclique number s is less than t (an induced K_s,s with
s >= t contains an induced K_t,t), so the polynomial p bounding the tree-independence number in
terms of the induced biclique number gives p(s) <= p(t), as p has natural coefficients.

The equivalence of the two questions is stated by Alon, Milanič and Rzążewski, and is the
edge e072 of relations.json in graph-conjectures.  It was formalized in graph-theory-rocq
(minor-theory/theories/conjectures/implications_X220.v). *)

From GraphTheory Require Import digraph sgraph.
From mathcomp Require Import boot ssralg poly.
From GC.GraphLib Require Import minor.
From GC.minor.AX_tree_independence_polynomial_induced_biclique_number Require Import
  main(AX_tree_independence_polynomial_induced_biclique_number).
From GC.minor.AX_tree_independence_polynomial_biclique_free Require Import
  main(AX_tree_independence_polynomial_biclique_free).

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** A polynomial with natural coefficients is nondecreasing on nat. *)
Lemma horner_rec_nat_homo (p : seq nat) : {homo horner_rec p : a b / a <= b}.
Proof. by move=> a b ab; elim: p => //= c p IH; apply: leq_add (leq_mul IH ab) (leqnn c). Qed.

Theorem AX_tree_independence_polynomial_induced_biclique_number_implies_AX_tree_independence_polynomial_biclique_free :
  AX_tree_independence_polynomial_induced_biclique_number ->
  AX_tree_independence_polynomial_biclique_free.
Proof.
move=> hA m _; have [p hp] := hA m; exists p => t G free mu.
have [s [[i] maxs]] := induced_biclique_number_exists G.
have st : s <= t.
  rewrite leqNgt; apply/negP => /ltnW ts; apply: free.
  exact: inhabits (isubgraph_comp (isubgraph_KB ts ts) i).
apply: tree_independence_leW (horner_rec_nat_homo p st) _.
exact: hp mu (conj (inhabits i) maxs).
Qed.

Check (AX_tree_independence_polynomial_induced_biclique_number_implies_AX_tree_independence_polynomial_biclique_free :
  GC.minor.AX_tree_independence_polynomial_induced_biclique_number.main.AX_tree_independence_polynomial_induced_biclique_number ->
  GC.minor.AX_tree_independence_polynomial_biclique_free.main.AX_tree_independence_polynomial_biclique_free).
Print Assumptions AX_tree_independence_polynomial_induced_biclique_number_implies_AX_tree_independence_polynomial_biclique_free.
