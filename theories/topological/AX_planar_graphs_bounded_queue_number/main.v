(** * Queue number of planar graphs

Joret, Micek, Wiechert, "Sparsity and dimension", arXiv:1507.01120, where it is mentioned as an open
problem on queue layouts (1507.01120__00).

A queue layout of a graph is a linear order of its vertices with a colouring of its edges such that
no two edges of the same colour are nested, where an edge cd is nested inside an edge ab if
a < c < d < b.  The queue number of a graph is the minimum number of colours in a queue layout.

Problem: decide whether planar graphs have bounded queue number.

The proposition states the positive answer: there is a constant k such that every planar graph has
queue number at most k.

Encoding.  Graphs are finite and simple.  Planarity is the absence of minors K_5 and K_3,3 (Wagner's
theorem).  The linear order is given by an injective map from the vertices to the integers. *)

From GraphTheory Require Import digraph sgraph minor.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/topological.v *)

(** [G] is planar: it has no minor [K_5] or [K_3,3]. *)
Definition planar (G : sgraph) : Prop :=
  ~ minor G 'K_5 /\ ~ minor G (KB 3 3).

(** The queue number of [G] is at most [k]: for some linear order of the vertices, the edges can
    be given [k] colours so that no edge [c d] is nested inside an edge [a b] of the same
    colour. *)
Definition queue_number_le (G : sgraph) (k : nat) : Prop :=
  exists (ord : G -> nat) (q : {set G} -> nat),
    [/\ injective ord,
        (forall e : {set G}, e \in E(G) -> q e < k) &
        forall a b c d : G,
          a -- b -> c -- d -> q [set a; b] = q [set c; d] ->
          ord a < ord c -> ord c < ord d -> ord d < ord b -> False].

(** ** Statement *)

Definition AX_planar_graphs_bounded_queue_number : Prop :=
  exists k : nat, forall G : sgraph, planar G -> queue_number_le G k.
