(** * Majority choosability of digraphs

Kreutzer, Oum, Seymour, van der Zypen, Wood, "Majority colourings of digraphs", 2016,
arXiv:1608.03040, Open Problem 7 (1608.03040__06).

A majority colouring of a digraph is a (not necessarily proper) colouring of its vertices such that,
for every vertex v, at most half of the out-neighbours of v have the same colour as v.  A digraph is
majority c-choosable if, for every assignment of a list L(v) of at least c colours to each vertex v,
it has a majority colouring where the colour of each vertex v is in L(v).

Question: is every digraph majority c-choosable for some constant c?

Encoding.  The positive answer is stated.  Digraphs are those of GraphTheory ([diGraph]: a finite
type of vertices with a boolean relation [--]) without loops; digons are allowed.  The colours form
an arbitrary finite set. *)

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

(** [D] is majority [c]-choosable: it has a majority colouring from all lists of size at least
    [c]. *)
Definition majority_choosable (D : diGraph) (c : nat) : Prop :=
  forall (C : finType) (L : D -> {set C}),
    (forall v : D, c <= #|L v|) ->
    exists col : D -> C, (forall v : D, col v \in L v) /\ majority_coloring 2 col.

(** ** Statement *)

Definition AX_majority_coloring_digraphs_choosability_constant : Prop :=
  exists c : nat,
    0 < c /\ forall D : diGraph, irreflexive (@edge_rel D) -> majority_choosable D c.
