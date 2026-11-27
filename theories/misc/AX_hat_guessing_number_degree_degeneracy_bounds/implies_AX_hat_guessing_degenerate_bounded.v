(** * Bounds of the hat guessing number by degree and degeneracy imply the degeneracy bound

The first proposition is the positive answer to the three parts of Problem 1.4 of Alon,
Ben-Eliezer, Shangguan and Tamo; its part (ii), a bound of the hat guessing number of
d-degenerate graphs in terms of d, is exactly the second proposition, a conjecture of Alon and
Chizewer.

The implication is the edge e061 of relations.json in graph-conjectures.  It was formalized in
graph-theory-rocq (graph-theory-misc/theories/conjectures/implications_X227.v). *)

From GraphTheory Require Import digraph sgraph.
From mathcomp Require Import boot.
From GC.misc.AX_hat_guessing_number_degree_degeneracy_bounds Require Import
  main(AX_hat_guessing_number_degree_degeneracy_bounds).
From GC.misc.AX_hat_guessing_degenerate_bounded Require Import
  main(AX_hat_guessing_degenerate_bounded).

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Theorem AX_hat_guessing_number_degree_degeneracy_bounds_implies_AX_hat_guessing_degenerate_bounded :
  AX_hat_guessing_number_degree_degeneracy_bounds -> AX_hat_guessing_degenerate_bounded.
Proof. by case=> _ [f2 bound2] _; exists f2. Qed.

Check (AX_hat_guessing_number_degree_degeneracy_bounds_implies_AX_hat_guessing_degenerate_bounded :
  GC.misc.AX_hat_guessing_number_degree_degeneracy_bounds.main.AX_hat_guessing_number_degree_degeneracy_bounds ->
  GC.misc.AX_hat_guessing_degenerate_bounded.main.AX_hat_guessing_degenerate_bounded).

Print Assumptions
  AX_hat_guessing_number_degree_degeneracy_bounds_implies_AX_hat_guessing_degenerate_bounded.
