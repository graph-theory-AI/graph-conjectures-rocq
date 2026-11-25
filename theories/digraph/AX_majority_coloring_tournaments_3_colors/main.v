(** * Majority 3-colourings of tournaments

Kreutzer, Oum, Seymour, van der Zypen, Wood, "Majority colourings of digraphs", arXiv:1608.03040,
Open Problem 2 (1608.03040__03).

A majority colouring of a digraph is a colouring of the vertices, not necessarily proper, such that
each vertex v has the colour of at most half of its out-neighbours.
A tournament is an orientation of a complete graph.

Open Problem 2: does every tournament have a majority colouring with three colours?  The proposition
states the positive answer.

Encoding.  Tournaments are digraphs of GraphTheory ([diGraph]: a finite type of vertices with a
boolean relation [--]) satisfying the predicate [tournament].  Colours are elements of ['I_3], and
the condition is [2 * s <= outdeg v], where s is the number of out-neighbours with the colour of v
(see [majority_coloring]). *)

From GraphTheory Require Import digraph.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/digraph.v *)

(** [D] is a tournament: it has no loop, and exactly one arc between any two distinct vertices. *)
Definition tournament (D : diGraph) : Prop :=
  irreflexive (@edge_rel D) /\ forall x y : D, (x != y) = (x -- y) (+) (y -- x).

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

Definition AX_majority_coloring_tournaments_3_colors : Prop :=
  forall T : diGraph, tournament T -> exists col : T -> 'I_3, majority_coloring 2 col.
