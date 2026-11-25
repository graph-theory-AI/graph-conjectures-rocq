(** * Kotzig's unique k-path conjecture

Kotzig; Bondy, Murty, "Graph Theory", Appendix A, problem 62.

The length of a path is its number of edges.

Conjecture: for k >= 3, there is no graph in which every pair of vertices is connected by a unique
path of length k.

Encoding.  Graphs are simple, and have at least two vertices (otherwise the property is trivially
true).  The pairs consist of two distinct vertices x and y.  A path from x to y is the list of its
vertices, starting after x. *)

From GraphTheory Require Import digraph sgraph.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions specific to the conjecture *)

(** [x :: p] is a path (without repetition) of length [k] from [x] to [y]. *)
Definition path_of_length (G : sgraph) (k : nat) (x y : G) (p : seq G) : bool :=
  [&& path (--) x p, size p == k, uniq (x :: p) & last x p == y].

(** ** Statement *)

Definition BM_kotzig_unique_k_path_nonexistence : Prop :=
  forall (k : nat) (G : sgraph),
    3 <= k -> 1 < #|G| ->
    ~ (forall x y : G, x != y -> exists! p : seq G, path_of_length k x y p).
