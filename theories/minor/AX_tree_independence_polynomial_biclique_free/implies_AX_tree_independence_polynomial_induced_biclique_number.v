(** * Polynomial bound for K_t,t-free graphs implies the bound by the induced biclique number

If the induced biclique number of G is t, then G has no induced K_t+1,t+1, so the polynomial p
bounding the tree-independence number of K_t,t-free graphs gives the bound p(1 + t), the value at
t of the polynomial p(1 + X), which has natural coefficients.  The bound m on the induced matching
treewidth must be positive for the hypothesis: it is applied to m + 1.

The equivalence of the two questions is stated by Alon, Milanič and Rzążewski, and is the
edge e072 of relations.json in graph-conjectures.  It was formalized in graph-theory-rocq
(minor-theory/theories/conjectures/implications_X220.v). *)

From GraphTheory Require Import sgraph.
From mathcomp Require Import boot ssralg poly.
From GC.GraphLib Require Import minor.
From GC.minor.AX_tree_independence_polynomial_biclique_free Require Import
  main(AX_tree_independence_polynomial_biclique_free).
From GC.minor.AX_tree_independence_polynomial_induced_biclique_number Require Import
  main(AX_tree_independence_polynomial_induced_biclique_number).

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.

Theorem AX_tree_independence_polynomial_biclique_free_implies_AX_tree_independence_polynomial_induced_biclique_number :
  AX_tree_independence_polynomial_biclique_free ->
  AX_tree_independence_polynomial_induced_biclique_number.
Proof.
move=> hB m; have [p hp] := hB m.+1 isT; exists (Poly p \Po (1%:P + 'X)) => G t mu [_ maxt].
(* The value at t of p(1 + X) is p(1 + t). *)
rewrite -[horner_rec _ _]/((_ \Po _).[t]) horner_comp hornerD hornerC hornerX horner_Poly.
apply: hp; last exact: induced_matching_tw_leW (leqnSn m) mu.
by move/maxt; rewrite ltnn.
Qed.

Check (AX_tree_independence_polynomial_biclique_free_implies_AX_tree_independence_polynomial_induced_biclique_number :
  GC.minor.AX_tree_independence_polynomial_biclique_free.main.AX_tree_independence_polynomial_biclique_free ->
  GC.minor.AX_tree_independence_polynomial_induced_biclique_number.main.AX_tree_independence_polynomial_induced_biclique_number).
Print Assumptions AX_tree_independence_polynomial_biclique_free_implies_AX_tree_independence_polynomial_induced_biclique_number.
