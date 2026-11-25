(** * Chromatic number and maximum degree of triangle-free graphs

Kostochka, Reed; Reed, "ω, Δ, and χ", J. Graph Theory 27 (1998); Open Problem Garden,
bounding_the_chromatic_number_of_triangle_free_graphs_with_fixed_maximum_degree.

Conjecture: a triangle-free graph of maximum degree Δ has chromatic number at most ⌈Δ/2⌉ + 2.

Encoding.  Graphs are finite and simple. *)

From GraphTheory Require Import digraph sgraph coloring.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

(** The ceiling of [a / b] (0 if [b = 0]). *)
Definition ceil_div (a b : nat) : nat := (a + b - 1) %/ b.

(** The maximum degree of [G] (0 if [G] is empty). *)
Definition Delta (G : sgraph) : nat := \max_(x : G) #|N(x)|.

(** [G] has no triangle. *)
Definition triangle_free (G : sgraph) : Prop :=
  forall x y z : G, x -- y -> y -- z -> z -- x -> False.

(** ** Statement *)

Definition OPG_triangle_free_chromatic_half_max_degree : Prop :=
  forall G : sgraph, triangle_free G -> χ([set: G]) <= ceil_div (Delta G) 2 + 2.
