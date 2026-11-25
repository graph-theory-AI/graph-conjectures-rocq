(** * Three-chromatic (0,2)-graphs

Payan, "On the chromatic number of cube-like graphs", Discrete Math. 103 (1992); Open Problem
Garden, three_chromatic_0_2_graphs.

A (0,2)-graph is a graph such that any two distinct vertices have either 0 or 2 common neighbours.

Question: are there any (0,2)-graphs with chromatic number exactly 3?

The proposition states the positive answer: such a graph exists.

Encoding.  Graphs are finite and simple.  Connectivity is not assumed, which is not a restriction:
a component of chromatic number 3 is also a (0,2)-graph. *)

From GraphTheory Require Import digraph sgraph coloring.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

(** The common neighbours of [u] and [v]. *)
Definition common_neigh (G : sgraph) (u v : G) : {set G} := N(u) :&: N(v).

(** ** Definitions specific to the conjecture *)

(** [G] is a (0,2)-graph. *)
Definition zero_two_graph (G : sgraph) : Prop :=
  forall u v : G, u != v -> #|common_neigh u v| = 0 \/ #|common_neigh u v| = 2.

(** ** Statement *)

Definition OPG_0_2_graphs_chromatic_number_3 : Prop :=
  exists G : sgraph, zero_two_graph G /\ χ([set: G]) = 3.
