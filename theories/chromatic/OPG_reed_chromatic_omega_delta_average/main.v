(** * Reed's conjecture on ω, Δ and χ

Reed, "ω, Δ, and χ", J. Graph Theory 27 (1998); Open Problem Garden,
reeds_omega_delta_and_chi_conjecture.

Conjecture: χ(G) <= ⌈(Δ(G) + 1 + ω(G)) / 2⌉ for every graph G, where Δ(G) is the maximum degree
and ω(G) is the clique number.

Encoding.  Graphs are finite, simple and nonempty.  The inequality is expressed as
2 χ(G) <= Δ(G) + 1 + ω(G) + 1, which is equivalent since 2 χ(G) is even. *)

From GraphTheory Require Import digraph sgraph coloring.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

(** The maximum degree of [G] (0 if [G] is empty). *)
Definition Delta (G : sgraph) : nat := \max_(x : G) #|N(x)|.

(** ** Statement *)

Definition OPG_reed_chromatic_omega_delta_average : Prop :=
  forall G : sgraph, 0 < #|G| ->
    2 * χ([set: G]) <= Delta G + 1 + ω([set: G]) + 1.
