(** * Majority 3-colourings of digraphs

Kreutzer, Oum, Seymour, van der Zypen, Wood, "Majority colourings of digraphs", arXiv:1608.03040,
Conjecture 2 (1608.03040__00).

A majority colouring of a digraph is a colouring of the vertices, not necessarily proper, such that
each vertex v has the colour of at most half of its out-neighbours.

Conjecture 2: every digraph has a majority colouring with three colours.

Encoding.  Digraphs are those of GraphTheory ([diGraph]): a finite type of vertices with a boolean
relation [--].  They have no loop here, but digons are allowed.  Colours are elements of ['I_3], and
the condition is [2 * s <= outdeg v], where s is the number of out-neighbours with the colour of v
(see [majority_coloring]). *)

From GraphTheory Require Import digraph.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/digraph.v *)

(** Out-degree. *)
Definition outdeg (D : diGraph) (v : D) : nat := #|N(v)|.

(** The out-neighbours of [v] with the colour of [v]. *)
Definition same_color_outneigh (D : diGraph) (C : eqType) (col : D -> C) (v : D) : {set D} :=
  [set w in N(v) | col w == col v].

(** [1/k]-majority colouring: each vertex has the colour of at most [1/k] of its
    out-neighbours.  The majority colourings are those with [k = 2]. *)
Definition majority_coloring (D : diGraph) (C : eqType) (k : nat) (col : D -> C) : bool :=
  [forall v : D, k * #|same_color_outneigh col v| <= outdeg v].

(** ** Statement *)

Definition AX_majority_coloring_digraphs_3_colors : Prop :=
  forall D : diGraph, irreflexive (@edge_rel D) ->
    exists col : D -> 'I_3, majority_coloring 2 col.
