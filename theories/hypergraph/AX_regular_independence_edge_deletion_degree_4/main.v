(** * Regular graphs with independence number stable under deletion of the ends of d - 1 edges

Clow, Haxell, Mohar, "A counterexample to a conjecture of Lovász", arXiv:2505.05339, Question 4.2
(2505.05339__01).

The independence number of a graph G is denoted by α(G).

Question 4.2: does there exist a d-regular d-edge-colourable graph G, where d >= 4, such that
α(G) = α(G - {u_1, ..., u_(d-1), v_1, ..., v_(d-1)}) for all edges u_1 v_1, ..., u_(d-1) v_(d-1)?

The proposition states that the answer is yes.

Encoding.  Graphs are finite and simple.  G is nonempty (the empty graph is a trivial solution).
The d - 1 edges are not assumed to be distinct, which changes nothing. *)

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

Definition AX_regular_independence_edge_deletion_degree_4 : Prop :=
  exists (d : nat) (G : sgraph),
    [/\ 4 <= d, 0 < #|G|, regular G d,
        exists col : {set G} -> 'I_d, proper_edge_coloring col
      & forall u v : 'I_d.-1 -> G, (forall i, u i -- v i) ->
          α([set: G]) = α([set: G] :\: ([set u i | i in 'I_d.-1] :|: [set v i | i in 'I_d.-1]))].
