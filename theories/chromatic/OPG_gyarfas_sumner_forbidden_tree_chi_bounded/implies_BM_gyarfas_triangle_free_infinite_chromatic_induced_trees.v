(** * The Gyárfás-Sumner conjecture implies its triangle-free case

A triangle-free graph has clique number at most 2.  Hence, if f is a χ-bounding function of the
graphs with no induced T, then f(0) + f(1) + f(2) bounds the chromatic number of the triangle-free
graphs with no induced T.

This is the edge e229 of relations.json in graph-conjectures.  It was formalized in
graph-theory-rocq (chromatic-theory/theories/conjectures/implications_X213.v). *)

From GraphTheory Require Import digraph sgraph coloring.
From mathcomp Require Import boot.
From GC.chromatic.OPG_gyarfas_sumner_forbidden_tree_chi_bounded Require Import
  main(OPG_gyarfas_sumner_forbidden_tree_chi_bounded).
From GC.chromatic.BM_gyarfas_triangle_free_infinite_chromatic_induced_trees Require Import
  main(BM_gyarfas_triangle_free_infinite_chromatic_induced_trees).
From GC.GraphLib Require Import chromatic(triangle_free_omega).

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Theorem OPG_gyarfas_sumner_forbidden_tree_chi_bounded_implies_BM_gyarfas_triangle_free_infinite_chromatic_induced_trees :
  OPG_gyarfas_sumner_forbidden_tree_chi_bounded ->
  BM_gyarfas_triangle_free_infinite_chromatic_induced_trees.
Proof.
move=> GS T Tt; have [f Hf] := GS T Tt; exists (\sum_(i < 3) f i) => G tf free.
apply: leq_trans (Hf G free) _; have w3 : ω([set: G]) < 3 := triangle_free_omega tf.
by rewrite (bigD1 (Ordinal w3)) //= leq_addr.
Qed.

Check (OPG_gyarfas_sumner_forbidden_tree_chi_bounded_implies_BM_gyarfas_triangle_free_infinite_chromatic_induced_trees :
  GC.chromatic.OPG_gyarfas_sumner_forbidden_tree_chi_bounded.main.OPG_gyarfas_sumner_forbidden_tree_chi_bounded ->
  GC.chromatic.BM_gyarfas_triangle_free_infinite_chromatic_induced_trees.main.BM_gyarfas_triangle_free_infinite_chromatic_induced_trees).
Print Assumptions OPG_gyarfas_sumner_forbidden_tree_chi_bounded_implies_BM_gyarfas_triangle_free_infinite_chromatic_induced_trees.
