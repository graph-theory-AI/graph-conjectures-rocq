(** * 1/k-majority colourings of digraphs with k+1 colours

Kreutzer, Oum, Seymour, van der Zypen, Wood, "Majority colourings of digraphs", arXiv:1608.03040,
Conjecture 9 (1608.03040__01).

Conjecture 9: for k >= 2, every digraph has a colouring of its vertices with k+1 colours such that
each vertex v has the colour of at most deg⁺(v)/k of its out-neighbours, where deg⁺(v) is the
out-degree of v.

Encoding.  Digraphs are those of GraphTheory ([diGraph]): a finite type of vertices with a boolean
relation [--].  They have no loop here, but digons are allowed.  Colours are elements of ['I_k.+1],
and the condition is [k * s <= outdeg v], where s is the number of out-neighbours with the colour
of v (see [majority_coloring]). *)

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

Definition AX_majority_coloring_digraphs_1_over_k : Prop :=
  forall (k : nat) (D : diGraph), 2 <= k -> irreflexive (@edge_rel D) ->
    exists col : D -> 'I_k.+1, majority_coloring k col.
