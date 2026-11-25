(** * Large chromatic number without 4-chromatic triangle-free induced subgraphs

Carbonero, Hompe, Moore, Spirkl, "A counterexample to a conjecture about triangle-free induced
subgraphs of graphs with large chromatic number", arXiv:2201.08204, Question 3.1 (2201.08204__00);
first asked by Davies.

Question 3.1: are there graphs with clique number 3 and arbitrarily large chromatic number all of
whose triangle-free induced subgraphs have chromatic number at most 3?

The proposition states the positive answer.

Encoding.  Graphs are finite and simple. *)

From GraphTheory Require Import digraph sgraph coloring.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

(** [G] has no triangle. *)
Definition triangle_free (G : sgraph) : Prop :=
  forall x y z : G, x -- y -> y -- z -> z -- x -> False.

(** ** Statement *)

Definition AX_clique_3_triangle_free_induced_bounded : Prop :=
  forall n : nat, exists G : sgraph,
    [/\ n <= χ([set: G]),
        ω([set: G]) = 3
      & forall S : {set G}, triangle_free (induced S) -> χ([set: induced S]) <= 3].
