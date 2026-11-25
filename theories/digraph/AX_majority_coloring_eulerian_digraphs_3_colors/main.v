(** * Majority 3-colourings of Eulerian digraphs

Kreutzer, Oum, Seymour, van der Zypen, Wood, "Majority colourings of digraphs", arXiv:1608.03040,
Open Problem 3 (1608.03040__04).

A majority colouring of a digraph is a colouring of the vertices, not necessarily proper, such that
each vertex v has the colour of at most half of its out-neighbours.
A digraph is Eulerian if the in-degree of each vertex is equal to its out-degree.

Open Problem 3: does every Eulerian digraph have a majority colouring with three colours?  The
proposition states the positive answer.

Encoding.  Digraphs are those of GraphTheory ([diGraph]): a finite type of vertices with a boolean
relation [--].  They have no loop here, but digons are allowed.  Colours are elements of ['I_3], and
the condition is [2 * s <= outdeg v], where s is the number of out-neighbours with the colour of v
(see [majority_coloring]).
Eulerian digraphs ([balanced_digraph]) are not assumed to be connected, which changes nothing as the
components can be coloured separately. *)

From GraphTheory Require Import digraph.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/digraph.v *)

(** Out-degree. *)
Definition outdeg (D : diGraph) (v : D) : nat := #|N(v)|.

(** In-degree. *)
Definition indeg (D : diGraph) (v : D) : nat := #|[set u | u -- v]|.

(** Each vertex has as many in-neighbours as out-neighbours (such a digraph is also called
    eulerian, connected or not). *)
Definition balanced_digraph (D : diGraph) : bool := [forall v : D, indeg v == outdeg v].

(** The out-neighbours of [v] with the colour of [v]. *)
Definition same_color_outneigh (D : diGraph) (C : eqType) (col : D -> C) (v : D) : {set D} :=
  [set w in N(v) | col w == col v].

(** [1/k]-majority colouring: each vertex has the colour of at most [1/k] of its
    out-neighbours.  The majority colourings are those with [k = 2]. *)
Definition majority_coloring (D : diGraph) (C : eqType) (k : nat) (col : D -> C) : bool :=
  [forall v : D, k * #|same_color_outneigh col v| <= outdeg v].

(** ** Statement *)

Definition AX_majority_coloring_eulerian_digraphs_3_colors : Prop :=
  forall D : diGraph, irreflexive (@edge_rel D) -> balanced_digraph D ->
    exists col : D -> 'I_3, majority_coloring 2 col.
