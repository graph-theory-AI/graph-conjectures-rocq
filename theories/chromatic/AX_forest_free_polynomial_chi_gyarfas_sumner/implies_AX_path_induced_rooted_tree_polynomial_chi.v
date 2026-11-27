(** * The polynomial Gyárfás-Sumner conjecture implies its version for path-induced copies

Let (T, r) be a rooted tree.  Every path of a tree is an induced path, hence an induced copy of T
in a graph G is a path-induced copy of (T, r).  The graphs with no path-induced copy of (T, r) thus
have no induced T, and they are polynomially χ-bounded.

This is the edge e041 of relations.json in graph-conjectures.  It was formalized in
graph-theory-rocq (chromatic-theory/theories/conjectures/implications_X218.v). *)

From GraphTheory Require Import digraph sgraph coloring.
From mathcomp Require Import boot.
From GC.chromatic.AX_forest_free_polynomial_chi_gyarfas_sumner Require Import
  main(AX_forest_free_polynomial_chi_gyarfas_sumner).
From GC.chromatic.AX_path_induced_rooted_tree_polynomial_chi Require Import
  main(AX_path_induced_rooted_tree_polynomial_chi).
From GC.GraphLib Require Import cycle(forest_path_nonadj).

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Theorem AX_forest_free_polynomial_chi_gyarfas_sumner_implies_AX_path_induced_rooted_tree_polynomial_chi :
  AX_forest_free_polynomial_chi_gyarfas_sumner -> AX_path_induced_rooted_tree_polynomial_chi.
Proof.
move=> P T r Tt; have [c [d h]] := P T Tt; exists c, d => G nocopy; apply: h => -[phi].
apply: nocopy; exists phi; split=> [|x y|p pth uq i j]; first exact: isubgraph_inj.
  by rewrite isubgraph_mono.
rewrite size_map => js ij; have iS : i < size (r :: p) := ltn_trans (ltnW ij) js.
by rewrite !(nth_map r) // isubgraph_mono; exact: (forest_path_nonadj r Tt.1 pth uq js ij).
Qed.

Check (AX_forest_free_polynomial_chi_gyarfas_sumner_implies_AX_path_induced_rooted_tree_polynomial_chi :
  GC.chromatic.AX_forest_free_polynomial_chi_gyarfas_sumner.main.AX_forest_free_polynomial_chi_gyarfas_sumner ->
  GC.chromatic.AX_path_induced_rooted_tree_polynomial_chi.main.AX_path_induced_rooted_tree_polynomial_chi).
Print Assumptions AX_forest_free_polynomial_chi_gyarfas_sumner_implies_AX_path_induced_rooted_tree_polynomial_chi.
