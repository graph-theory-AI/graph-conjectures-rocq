(** * Requests for 3-colourings of planar triangle-free graphs

Dvořák, Sereni, "Do triangle-free planar graphs have exponentially many 3-colorings?",
arXiv:1702.00588, Problem 1 (1702.00588__00).

A request graph consists of a graph G, two disjoint sets R_= and R_≠ of vertices of degree 2 of G
such that R_= ∪ R_≠ is an independent set, and positive rational weights w on R_= ∪ R_≠.  In a
proper 3-colouring of G, a request r ∈ R_= is satisfied if its two neighbours have the same colour,
and a request r ∈ R_≠ is satisfied if its two neighbours have different colours.  The colouring
satisfies an α-fraction of the requests if the satisfied requests have total weight at least
α w(R_= ∪ R_≠).

Problem 1: is there a positive real number α such that every planar triangle-free request graph
admits a 3-colouring satisfying an α-fraction of its requests?

The proposition states the positive answer.

Encoding.  Graphs are finite and simple.  Planarity is the absence of minors K_5 and K_3,3.  α is a
rational number p/q with 0 < p <= q, and weights are positive integers.  This is equivalent: α may
be decreased, and weights may be multiplied by a common denominator. *)

From GraphTheory Require Import digraph sgraph dom coloring minor.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

(** [G] has no triangle. *)
Definition triangle_free (G : sgraph) : Prop :=
  forall x y z : G, x -- y -> y -- z -> z -- x -> False.

(** ** Definitions copied from GraphLib/chromatic.v *)

(** [col] is a proper colouring of [G]. *)
Definition proper_coloring (G : sgraph) (C : finType) (col : G -> C) : bool :=
  coloring (preim_partition col [set: G]) [set: G].

(** ** Definitions copied from GraphLib/topological.v *)

(** [G] is planar: it has no minor [K_5] or [K_3,3]. *)
Definition planar (G : sgraph) : Prop :=
  ~ minor G 'K_5 /\ ~ minor G (KB 3 3).

(** ** Definitions specific to the conjecture *)

(** [x] and [y] are the two neighbours of [r]. *)
Definition request_pair (G : sgraph) (r x y : G) : bool := (x != y) && (N(r) == [set x; y]).

(** [Req] and [Rneq] are the disjoint sets of equality and inequality requests, their union is an
    independent set of vertices of degree 2, and [w] gives them positive weights. *)
Definition request_graph (G : sgraph) (Req Rneq : {set G}) (w : G -> nat) : Prop :=
  [/\ [disjoint Req & Rneq], stable (Req :|: Rneq)
    & forall r : G, r \in Req :|: Rneq -> #|N(r)| = 2 /\ 0 < w r].

(** The two neighbours of [r] have the same colour. *)
Definition eq_request_satisfied (G : sgraph) (col : G -> 'I_3) (r : G) : bool :=
  [exists x : G, [exists y : G, request_pair r x y && (col x == col y)]].

(** The two neighbours of [r] have different colours. *)
Definition neq_request_satisfied (G : sgraph) (col : G -> 'I_3) (r : G) : bool :=
  [exists x : G, [exists y : G, request_pair r x y && (col x != col y)]].

(** The total weight of the requests. *)
Definition request_weight (G : sgraph) (Req Rneq : {set G}) (w : G -> nat) : nat :=
  \sum_(r in Req) w r + \sum_(r in Rneq) w r.

(** The weight of the requests satisfied by [col]. *)
Definition satisfied_weight
    (G : sgraph) (Req Rneq : {set G}) (w : G -> nat) (col : G -> 'I_3) : nat :=
  \sum_(r in Req | eq_request_satisfied col r) w r +
  \sum_(r in Rneq | neq_request_satisfied col r) w r.

(** ** Statement *)

Definition AX_triangle_free_planar_3_coloring_requests : Prop :=
  exists p q : nat,
    [/\ 0 < p, p <= q
      & forall (G : sgraph) (Req Rneq : {set G}) (w : G -> nat),
          planar G -> triangle_free G -> request_graph Req Rneq w ->
          exists col : G -> 'I_3,
            proper_coloring col /\
            p * request_weight Req Rneq w <=
              q * satisfied_weight Req Rneq w col].
