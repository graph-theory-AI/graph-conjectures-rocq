(** * Neighbour sum distinguishing edge colourings with Δ + O(1) colours

Joret, Lochet, "Progress on the adjacent vertex distinguishing edge colouring conjecture",
arXiv:1804.06104, open problem (1804.06104__00).

A neighbour sum distinguishing colouring of a graph G is a proper edge colouring with positive
integers such that, for every edge uv, the sum of the colours of the edges incident to u differs
from the sum of the colours of the edges incident to v.

Problem: is there a bound Δ + O(1) on the number of colours (that is, colours in {1,...,Δ + O(1)})
required for a neighbour sum distinguishing colouring of a graph without isolated edge, where Δ is
its maximum degree?

The proposition states the positive answer, with one constant for all graphs.

Encoding.  Graphs are finite and simple.  The edges are sets of two vertices, and an edge colouring
is a map on the sets of vertices (its values elsewhere are irrelevant).  The colours are 0,...,k-1,
but 1 is added to each of them in the sums.  An edge is isolated if both its ends have degree 1
(such an edge is excluded because its ends always have the same sum).  There is no assumption
Δ >= 3, which changes only the constant. *)

From GraphTheory Require Import digraph sgraph.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

(** The maximum degree of [G] (0 if [G] is empty). *)
Definition Delta (G : sgraph) : nat := \max_(x : G) #|N(x)|.

(** ** Definitions copied from GraphLib/chromatic.v *)

(** [col] is a proper edge colouring. *)
Definition proper_edge_coloring (G : sgraph) (C : eqType) (col : {set G} -> C) : Prop :=
  forall x y z : G, x -- y -> x -- z -> y != z -> col [set x; y] != col [set x; z].

(** The sum of the colours of the edges incident to [v], the colours being numbered from 1. *)
Definition incident_sum
    (G : sgraph) (k : nat) (col : {set G} -> 'I_k) (v : G) : nat :=
  \sum_(e in [set e in E(G) | v \in e]) (val (col e)).+1.

(** [col] is neighbour sum distinguishing: adjacent vertices have different sums. *)
Definition neighbor_sum_distinct
    (G : sgraph) (k : nat) (col : {set G} -> 'I_k) : Prop :=
  forall x y : G, x -- y -> incident_sum col x != incident_sum col y.

(** ** Definitions specific to the conjecture *)

(** [G] has a proper edge colouring with [k] colours that is neighbour sum distinguishing. *)
Definition neighbour_sum_edge_colourable (G : sgraph) (k : nat) : Prop :=
  exists col : {set G} -> 'I_k,
    proper_edge_coloring col /\ neighbor_sum_distinct col.

(** Every edge of [G] has an end of degree at least 2. *)
Definition no_isolated_edge (G : sgraph) : Prop :=
  forall x y : G, x -- y -> 1 < #|N(x)| \/ 1 < #|N(y)|.

(** ** Statement *)

Definition AX_neighbor_sum_distinguishing_delta_plus_constant : Prop :=
  exists C : nat, forall G : sgraph,
    no_isolated_edge G -> neighbour_sum_edge_colourable G (Delta G + C).
