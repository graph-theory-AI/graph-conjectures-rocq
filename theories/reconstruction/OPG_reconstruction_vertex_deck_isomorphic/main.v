(** * Reconstruction conjecture

Kelly, "A congruence theorem for trees", Pacific J. Math. 7 (1957); Ulam, A collection of
mathematical problems (1960); Open Problem Garden, reconstruction_conjecture.

The deck of a graph G is the multiset of the graphs G - v up to isomorphism, for all the vertices v
of G.

Conjecture: if two graphs with at least 3 vertices have the same deck, then they are isomorphic.

Encoding.  Graphs are finite and simple.  Two graphs have the same deck if there is a bijection f
between their vertex sets such that G - v is isomorphic to H - f(v) for every vertex v of G. *)

From GraphTheory Require Import digraph sgraph.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/reconstruction.v *)

(** [G] and [H] have the same deck (they are hypomorphic). *)
Definition same_deck (G H : sgraph) : Prop :=
  exists f : G -> H,
    bijective f /\
    forall v : G, inhabited (induced [set~ v] ≃ induced [set~ f v]).

(** ** Statement *)

Definition OPG_reconstruction_vertex_deck_isomorphic : Prop :=
  forall G H : sgraph,
    3 <= #|G| -> 3 <= #|H| -> same_deck G H -> inhabited (G ≃ H).
