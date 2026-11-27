(** * Bounded treewidth of (C_4, diamond, theta, prism, even wheel, K_t)-free graphs implies
      bounded treewidth of (even hole, K_4, diamond)-free graphs

The 4-cycle, the thetas, the prisms and the even wheels contain even holes, hence an (even hole,
K_4, diamond)-free graph is (C_4, diamond, theta, prism, even wheel, K_4)-free, and the case t = 4
of the first statement bounds its treewidth.

The implication is the edge e051 of relations.json in graph-conjectures.  It was formalized in
graph-theory-rocq (minor-theory/theories/conjectures/implications_X42.v). *)

From GraphTheory Require Import preliminaries digraph sgraph coloring treewidth.
From mathcomp Require Import boot.
From GC.GraphLib Require Import ramsey.
From GC.minor.AX_c4_diamond_theta_prism_bounded_treewidth Require Import
  main(AX_c4_diamond_theta_prism_bounded_treewidth).
From GC.minor.AX_c4_diamond_theta_prism_bounded_treewidth Require even_holes.
From GC.minor.AX_even_hole_k4_diamond_free_treewidth Require Import
  main(AX_even_hole_k4_diamond_free_treewidth).

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Theorem AX_c4_diamond_theta_prism_bounded_treewidth_implies_AX_even_hole_k4_diamond_free_treewidth :
  AX_c4_diamond_theta_prism_bounded_treewidth -> AX_even_hole_k4_diamond_free_treewidth.
Proof.
move=> tw; have [c twc] := tw 4; exists c => G eh noK4 nodiamond; apply: twc => //.
- exact: even_holes.even_hole_free_C4.
- by move=> H /(even_holes.even_hole_free_theta eh).
- by move=> H /(even_holes.even_hole_free_prism eh).
- exact: even_holes.even_hole_free_even_wheel.
by rewrite ltnNge; apply/negP => /has_induced_copy_Kn.
Qed.

Check (AX_c4_diamond_theta_prism_bounded_treewidth_implies_AX_even_hole_k4_diamond_free_treewidth :
  GC.minor.AX_c4_diamond_theta_prism_bounded_treewidth.main.AX_c4_diamond_theta_prism_bounded_treewidth ->
  GC.minor.AX_even_hole_k4_diamond_free_treewidth.main.AX_even_hole_k4_diamond_free_treewidth).
Print Assumptions AX_c4_diamond_theta_prism_bounded_treewidth_implies_AX_even_hole_k4_diamond_free_treewidth.
