(** * Melnikov's valency-variety problem

Melnikov: Vizing, "Some unsolved problems in graph theory", Russian Math. Surveys 23 (1968); Open
Problem Garden, melnikovs_valency_variety_problem.

The valency-variety w(G) of a graph G is the number of different degrees in G.

Problem: is the chromatic number of any graph G with at least two vertices greater than
⌈⌊w(G)/2⌋ / (|V(G)| - w(G))⌉?

The proposition states the positive answer.

Encoding.  Graphs are finite and simple.  The denominator is positive, as a graph with at least
two vertices has two vertices of the same degree. *)

From GraphTheory Require Import digraph sgraph coloring.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

(** The ceiling of [a / b] (0 if [b = 0]). *)
Definition ceil_div (a b : nat) : nat := (a + b - 1) %/ b.

(** ** Definitions specific to the conjecture *)

(** The valency-variety of [G]. *)
Definition valency_variety (G : sgraph) : nat :=
  size (undup [seq #|N(x)| | x <- enum [set: G]]).

(** ** Statement *)

Definition OPG_melnikov_valency_variety_chromatic_bound : Prop :=
  forall G : sgraph, 2 <= #|G| ->
    ceil_div (valency_variety G %/ 2) (#|G| - valency_variety G) < χ([set: G]).
