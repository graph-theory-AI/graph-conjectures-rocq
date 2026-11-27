(** * Every forest is multibounding implies the Gyárfás-Sumner conjecture

Let T be a tree.  The complete d-partite graph K_d(1) with parts of size 1 is the complete graph
K_d, hence a graph G has no subgraph K_d(1) for d = ω(G) + 1.  Since T is multibounding, there is
a function c such that χ(G) <= c(d) 1^e = c(ω(G) + 1) for every graph G with no induced T.

This is the edge e035 of relations.json in graph-conjectures.  It was formalized in
graph-theory-rocq (chromatic-theory/theories/conjectures/implications_X218.v). *)

From GraphTheory Require Import digraph sgraph coloring.
From mathcomp Require Import boot.
From GC.chromatic.AX_forest_free_multibounding_chi_bound Require Import
  main(AX_forest_free_multibounding_chi_bound).
From GC.chromatic.OPG_gyarfas_sumner_forbidden_tree_chi_bounded Require Import
  main(OPG_gyarfas_sumner_forbidden_tree_chi_bounded).
From GC.GraphLib Require Import chromatic(complete_multipartite1_omega).

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Theorem AX_forest_free_multibounding_chi_bound_implies_OPG_gyarfas_sumner_forbidden_tree_chi_bounded :
  AX_forest_free_multibounding_chi_bound -> OPG_gyarfas_sumner_forbidden_tree_chi_bounded.
Proof.
move=> MB T [Tf _]; have [c [e He]] := MB T Tf.
exists (fun w => c w.+1) => G free; rewrite -[c _]muln1 -(exp1n (e (ω([set: G])).+1)).
by apply: He => // /complete_multipartite1_omega; rewrite ltnn.
Qed.

Check (AX_forest_free_multibounding_chi_bound_implies_OPG_gyarfas_sumner_forbidden_tree_chi_bounded :
  GC.chromatic.AX_forest_free_multibounding_chi_bound.main.AX_forest_free_multibounding_chi_bound ->
  GC.chromatic.OPG_gyarfas_sumner_forbidden_tree_chi_bounded.main.OPG_gyarfas_sumner_forbidden_tree_chi_bounded).
Print Assumptions AX_forest_free_multibounding_chi_bound_implies_OPG_gyarfas_sumner_forbidden_tree_chi_bounded.
