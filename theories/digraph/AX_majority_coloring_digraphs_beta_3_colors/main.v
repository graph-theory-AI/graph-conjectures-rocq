(** * 3-colourings with few out-neighbours of the same colour

Kreutzer, Oum, Seymour, van der Zypen, Wood, "Majority colourings of digraphs", 2016,
arXiv:1608.03040, Open Problem 1 (1608.03040__02).

Colourings of digraphs are not necessarily proper, and deg⁺(v) is the out-degree of v.

Question: is there a constant β < 1 such that every digraph has a 3-colouring where, for every
vertex v, at most β deg⁺(v) out-neighbours of v have the same colour as v?

Encoding.  The positive answer is stated.  Digraphs are those of GraphTheory ([diGraph]: a finite
type of vertices with a boolean relation [--]) without loops; digons are allowed.  Without loss of
generality, β = p/q for integers 0 <= p < q. *)

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

(** ** Statement *)

Definition AX_majority_coloring_digraphs_beta_3_colors : Prop :=
  exists p q : nat, p < q /\
    forall D : diGraph, irreflexive (@edge_rel D) ->
      exists col : D -> 'I_3,
        forall v : D, q * #|same_color_outneigh col v| <= p * outdeg v.
