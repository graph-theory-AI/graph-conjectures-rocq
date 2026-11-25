(** * TSP walks in subcubic graphs

Dvořák, Král', Mohar, "Graphic TSP in cubic graphs", arXiv:1608.07568, Conjecture 1
(1608.07568__00).

A graph is subcubic if all its vertices have degree at most three.  A TSP walk of a graph is a
closed walk visiting every vertex at least once.  Its length is its number of edges, counted with
multiplicity.

Conjecture: every 2-connected subcubic n-vertex graph with n_2 vertices of degree two has a TSP walk
of length at most (5/4) n + (1/4) n_2 - 1.

Encoding.  Graphs are finite and simple.  A 2-connected graph has more than two vertices.  A closed
walk is the sequence of its vertices, where the first one is repeated at the end.  The bound on the
length l is written 4 l + 4 <= 5 n + n_2. *)

From GraphTheory Require Import digraph sgraph connectivity.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

(** Every vertex has degree at most 3. *)
Definition subcubic (G : sgraph) : Prop := forall v : G, #|N(v)| <= 3.

(** ** Definitions copied from GraphLib/hamiltonicity.v *)

(** [w] is a TSP walk: a closed walk that visits all vertices. *)
Definition tsp_walk (G : sgraph) (w : seq G) : Prop :=
  exists x p,
    [/\ w = x :: p,
        path (--) x p,
        last x p = x
      & forall v : G, v \in w].

(** ** Definitions specific to the conjecture *)

(** The length of the walk [w]: its number of edges. *)
Definition walk_length (G : sgraph) (w : seq G) : nat := (size w).-1.

(** The number of vertices of degree 2. *)
Definition degree_two_count (G : sgraph) : nat := #|[set v : G | #|N(v)| == 2]|.

(** ** Statement *)

Definition AX_subcubic_tsp_walk_5_4_n : Prop :=
  forall G : sgraph, 2.-connected G -> subcubic G ->
    exists w : seq G,
      tsp_walk w /\ 4 * walk_length w + 4 <= 5 * #|G| + degree_two_count G.
