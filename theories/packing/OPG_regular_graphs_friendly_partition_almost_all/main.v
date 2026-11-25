(** * Friendly partitions

DeVos; Open Problem Garden, friendly_partitions.

A friendly partition of a graph is a partition of its vertices into two sets such that every vertex
has at least as many neighbours in its own class as in the other.

Problem: is it true that, for every r, all but finitely many r-regular graphs have friendly
partitions?

The proposition states the positive answer.

Encoding.  Graphs are finite and simple, and the two classes are nonempty.  "All but finitely many"
(up to isomorphism) means: all those with more than N vertices, for some N. *)

From GraphTheory Require Import digraph sgraph.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

(** Every vertex has degree [d]. *)
Definition regular (G : sgraph) (d : nat) : Prop := forall v : G, #|N(v)| = d.

(** ** Definitions copied from GraphLib/packing.v *)

(** The partition of the vertices into [A] and its complement is friendly: both parts are
    nonempty, and each vertex has at least as many neighbours in its own part as in the other
    one. *)
Definition friendly_partition (G : sgraph) (A : {set G}) : Prop :=
  [/\ A != set0, A != [set: G]
    & forall v : G,
        (v \in A -> #|N(v) :&: (~: A)| <= #|N(v) :&: A|) /\
        (v \notin A -> #|N(v) :&: A| <= #|N(v) :&: (~: A)|)].

(** ** Statement *)

Definition OPG_regular_graphs_friendly_partition_almost_all : Prop :=
  forall r : nat, exists N : nat,
    forall G : sgraph, regular G r -> N < #|G| -> exists A : {set G}, friendly_partition A.
