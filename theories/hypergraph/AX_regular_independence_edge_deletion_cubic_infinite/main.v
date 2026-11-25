(** * Cubic graphs with independence number stable under deletion of the ends of two edges

Clow, Haxell, Mohar, "A counterexample to a conjecture of Lovász", arXiv:2505.05339, Question 4.1
(2505.05339__00).

The independence number of a graph G is denoted by α(G).

Question 4.1: do there exist infinitely many 3-edge-colourable cubic graphs G such that
α(G) = α(G - {u,v,x,y}) for all edges uv and xy?

The proposition states that the answer is yes.

Encoding.  Graphs are finite, simple and taken up to isomorphism, so "infinitely many" means that
the number of vertices is unbounded.  The graphs are assumed to be connected: otherwise disjoint
copies of a single such graph would do.  uv = xy is allowed, which changes nothing. *)

From GraphTheory Require Import digraph sgraph coloring.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

(** Every vertex has degree [d]. *)
Definition regular (G : sgraph) (d : nat) : Prop := forall v : G, #|N(v)| = d.

(** ** Definitions copied from GraphLib/chromatic.v *)

(** [col] is a proper edge colouring. *)
Definition proper_edge_coloring (G : sgraph) (C : eqType) (col : {set G} -> C) : Prop :=
  forall x y z : G, x -- y -> x -- z -> y != z -> col [set x; y] != col [set x; z].

(** ** Statement *)

Definition AX_regular_independence_edge_deletion_cubic_infinite : Prop :=
  forall N : nat, exists G : sgraph,
    [/\ N <= #|G|, connected [set: G], regular G 3,
        exists col : {set G} -> 'I_3, proper_edge_coloring col
      & forall u v x y : G, u -- v -> x -- y ->
          α([set: G]) = α([set: G] :\: [set u; v; x; y])].
