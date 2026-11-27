(** * The 7/8 bound for induced 2-degenerate subgraphs implies the 5/6 bound

Since 7/8 >= 5/6, a set S of vertices inducing a 2-degenerate subgraph of a triangle-free planar
graph on at least 7/8 of its n vertices also has at least 5/6 of them: 35 n <= 40 |S| <= 42 |S|.

The implication is the edge e082 of relations.json in graph-conjectures.  It was formalized in
graph-theory-rocq (chromatic-theory/theories/conjectures/implications_X219.v). *)

From GraphTheory Require Import digraph sgraph.
From mathcomp Require Import boot.
From GC.chromatic.AX_triangle_free_planar_2_degenerate_7_8 Require Import
  main(AX_triangle_free_planar_2_degenerate_7_8).
From GC.chromatic.AX_triangle_free_planar_2_degenerate_5_6 Require Import
  main(AX_triangle_free_planar_2_degenerate_5_6).

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Theorem AX_triangle_free_planar_2_degenerate_7_8_implies_AX_triangle_free_planar_2_degenerate_5_6 :
  AX_triangle_free_planar_2_degenerate_7_8 -> AX_triangle_free_planar_2_degenerate_5_6.
Proof.
move=> H G pl tf; have [S [big deg]] := H G pl tf; exists S; split => //.
by rewrite -(leq_pmul2l (isT : 0 < 7)) mulnCA (leq_trans (leq_mul (leqnn 5) big)) // !mulnA
  leq_mul2r orbT.
Qed.

Check
  (AX_triangle_free_planar_2_degenerate_7_8_implies_AX_triangle_free_planar_2_degenerate_5_6 :
GC.chromatic.AX_triangle_free_planar_2_degenerate_7_8.main.AX_triangle_free_planar_2_degenerate_7_8
  ->
GC.chromatic.AX_triangle_free_planar_2_degenerate_5_6.main.AX_triangle_free_planar_2_degenerate_5_6
  ).
Print Assumptions
  AX_triangle_free_planar_2_degenerate_7_8_implies_AX_triangle_free_planar_2_degenerate_5_6.
