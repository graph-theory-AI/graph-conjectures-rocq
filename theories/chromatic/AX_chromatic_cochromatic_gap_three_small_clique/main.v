(** * Gap between the chromatic and cochromatic numbers of K_5-free graphs

Steiner, "On the difference between the chromatic and cochromatic number", arXiv:2408.02400,
Problem 1.5 (2408.02400__00).

The cochromatic number ζ(G) of a graph G is the minimum size of a partition of V(G) into sets that
are stable or cliques.

Problem 1.5: let k >= 5.  Is there a graph G_k with ω(G_k) < 5, ζ(G_k) = k and χ(G_k) = ζ(G_k) + 3?

The proposition states the positive answer, for every k >= 5.

Encoding.  Graphs are finite and simple.  "ζ(G) = k" is a relation between G and k. *)

From GraphTheory Require Import digraph sgraph dom coloring.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/chromatic.v *)

(** [G] has a colouring with [k] colours whose classes are cliques or stable sets. *)
Definition cocolorable (G : sgraph) (k : nat) : Prop :=
  exists col : G -> 'I_k,
    forall i : 'I_k,
      let S := [set v : G | col v == i] in
      clique S \/ stable S.

(** The cochromatic number of [G] is [k]. *)
Definition cochromatic_number (G : sgraph) (k : nat) : Prop :=
  cocolorable G k /\
  forall j : nat, cocolorable G j -> k <= j.

(** ** Statement *)

Definition AX_chromatic_cochromatic_gap_three_small_clique : Prop :=
  forall k : nat, 5 <= k ->
    exists G : sgraph,
      [/\ ω([set: G]) < 5, cochromatic_number G k & χ([set: G]) = k + 3].
