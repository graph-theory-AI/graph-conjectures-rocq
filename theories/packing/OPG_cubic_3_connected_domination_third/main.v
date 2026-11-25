(** * Domination in cubic 3-connected graphs

Reed; Open Problem Garden, domination_in_cubic_graphs.

A set D of vertices of a graph G is dominating if every vertex is in D or has a neighbour in D.
The domination number γ(G) is the minimum size of a dominating set.  A graph is cubic if all its
degrees are 3.

Problem: does every 3-connected cubic graph G satisfy γ(G) <= ⌈|V(G)|/3⌉?

The proposition states the positive answer.

Encoding.  Graphs are finite and simple. *)

From GraphTheory Require Import digraph sgraph connectivity.
From GraphTheory Require dom.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

(** The ceiling of [a / b] (0 if [b = 0]). *)
Definition ceil_div (a b : nat) : nat := (a + b - 1) %/ b.

(** Every vertex has degree [d]. *)
Definition regular (G : sgraph) (d : nat) : Prop := forall v : G, #|N(v)| = d.

(** ** Statement *)

Definition OPG_cubic_3_connected_domination_third : Prop :=
  forall G : sgraph,
    regular G 3 -> 3.-connected G -> dom.gamma G <= ceil_div #|G| 3.
