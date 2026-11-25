(** * Star chromatic index of subcubic graphs

Dvořák, Mohar, Šámal, "Star chromatic index", J. Graph Theory 72 (2013), arXiv:1011.3376; Open
Problem Garden, star_chromatic_index_of_cubic_graphs.

The star chromatic index χ_s'(G) of a graph G is the minimum number of colours of a proper edge
colouring of G such that no path or cycle of length four is bicoloured.

Question: is it true that χ_s'(G) <= 6 for every (sub)cubic graph G?

The proposition states the positive answer, for all graphs of maximum degree at most 3.

Encoding.  Graphs are finite and simple.  The length of a path or cycle is its number of edges.
An edge colouring is a map on the sets of vertices, whose values on the sets that are not edges are
irrelevant. *)

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

(** [col] is a star edge colouring: it is proper, and no path or cycle with four edges has only
    two colours. *)
Definition star_edge_coloring (G : sgraph) (C : finType) (col : {set G} -> C) : Prop :=
  [/\ proper_edge_coloring col,
      (forall a b c d e : G,
         uniq [:: a; b; c; d; e] -> a -- b -> b -- c -> c -- d -> d -- e ->
         2 < #|[set col [set a; b]; col [set b; c]; col [set c; d]; col [set d; e]]|)
    & (forall a b c d : G,
         uniq [:: a; b; c; d] -> a -- b -> b -- c -> c -- d -> d -- a ->
         2 < #|[set col [set a; b]; col [set b; c]; col [set c; d]; col [set d; a]]|)].

(** [G] is star [k]-edge-colourable ([0 < k] is meant). *)
Definition star_edge_colorable (G : sgraph) (k : nat) : Prop :=
  exists col : {set G} -> 'I_k, star_edge_coloring col.

(** ** Statement *)

Definition OPG_star_chromatic_index_cubic_6 : Prop :=
  forall G : sgraph, Delta G <= 3 -> star_edge_colorable G 6.
