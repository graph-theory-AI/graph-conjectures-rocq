(** * Covering H-free graphs with restricted sets

Chudnovsky, Scott, Seymour, Spirkl, "Strengthening Rödl's theorem", arXiv:2105.07370, union variant
of Theorem 1.4 (2105.07370__00).

A graph is H-free if it has no induced subgraph isomorphic to H.  A set X of vertices of G is
ε-restricted if one of G[X] and its complement has maximum degree at most ε|X|.

Statement: for every graph H and every ε > 0, there is an integer N such that the vertex set of
every H-free graph is the union of at most N ε-restricted sets (not necessarily disjoint).

Encoding.  Graphs are finite and simple.  It suffices to consider rational numbers ε = a/b.
The union of at most N sets is given by N sets, which may be equal or empty (the empty set is
ε-restricted). *)

From GraphTheory Require Import digraph sgraph.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

(** The maximum degree of [G] (0 if [G] is empty). *)
Definition Delta (G : sgraph) : nat := \max_(x : G) #|N(x)|.

(** [G] has an induced subgraph isomorphic to [H]. *)
Definition has_induced_copy (G H : sgraph) : Prop := inhabited (H ⇀ G).

(** [G] has no induced subgraph isomorphic to [H]. *)
Definition induced_free (G H : sgraph) : Prop := ~ has_induced_copy G H.

(** ** Definitions copied from GraphLib/extremal.v *)

(** [X] is [a/b]-restricted: in [G] or in its complement, the maximum degree of the subgraph
    induced by [X] is at most [(a / b) |X|]. *)
Definition restricted_set (G : sgraph) (a b : nat) (X : {set G}) : Prop :=
  b * Delta (induced X) <= a * #|X| \/ b * Delta (@induced (compl G) X) <= a * #|X|.

(** ** Statement *)

Definition AX_rodl_h_free_restricted_union_cover : Prop :=
  forall (H : sgraph) (a b : nat), 0 < a -> 0 < b ->
    exists N : nat, forall G : sgraph, induced_free G H ->
      exists P : 'I_N -> {set G},
        (forall v : G, exists i : 'I_N, v \in P i) /\ (forall i : 'I_N, restricted_set a b (P i)).
