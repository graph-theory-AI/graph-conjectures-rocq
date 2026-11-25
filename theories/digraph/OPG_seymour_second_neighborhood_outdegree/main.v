(** * Seymour's second neighbourhood conjecture

Seymour; Open Problem Garden, seymours_second_neighbourhood_conjecture.

An oriented graph is a digraph without loop and without digon.  The second out-degree of a vertex v
is the number of vertices at distance exactly two from v (by directed paths starting at v).

Conjecture: every oriented graph has a vertex whose out-degree is at most its second out-degree.

Encoding.  Digraphs are those of GraphTheory ([diGraph]): a finite type of vertices with a boolean
relation [--].  The digraph is finite and nonempty, which is implicit in the source.  The notations
[N(v)], [N[v]] and [NS(A)] of GraphTheory are the out-neighbourhood of v, the same with v added, and
the union of the out-neighbourhoods of the vertices of A. *)

From GraphTheory Require Import digraph.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/digraph.v *)

(** [D] is oriented: it has no digon, and no loop. *)
Definition oriented (D : diGraph) : Prop :=
  forall x y : D, x -- y -> ~~ (y -- x).

(** Out-degree. *)
Definition outdeg (D : diGraph) (v : D) : nat := #|N(v)|.

(** Second out-neighbourhood: the vertices at distance exactly two from [v]. *)
Definition second_outneigh (D : diGraph) (v : D) : {set D} :=
  NS(N(v)) :\: N[v].

(** ** Statement *)

Definition OPG_seymour_second_neighborhood_outdegree : Prop :=
  forall D : diGraph, oriented D -> 0 < #|D| ->
    exists v : D, outdeg v <= #|second_outneigh v|.
