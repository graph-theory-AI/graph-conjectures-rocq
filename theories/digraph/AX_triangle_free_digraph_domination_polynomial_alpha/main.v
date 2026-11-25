(** * Domination in digraphs without directed triangle

Harutyunyan, Le, Newman, Thomassé, "Domination and fractional domination in digraphs", 2017,
arXiv:1708.00423, Conjecture 3.5 (1708.00423__00).

Digraphs have no loop and at most one arc between any two vertices.  The independence number α(G)
is that of the underlying graph.  A set S of vertices is dominating if every vertex is in S or is an
out-neighbour of a vertex of S; the domination number γ(G) is the minimum size of a dominating set.
A digraph is directed-triangle-free if it contains no cyclically oriented triangle.

Conjecture: there is an integer ℓ such that γ(G) <= α(G)^ℓ for every directed-triangle-free
digraph G.

Encoding.  Digraphs are those of GraphTheory ([diGraph]: a finite type of vertices with a boolean
relation [--]), without loop or digon ([oriented]). *)

From GraphTheory Require Import digraph.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/digraph.v *)

(** [D] is oriented: it has no digon, and no loop. *)
Definition oriented (D : diGraph) : Prop :=
  forall x y : D, x -- y -> ~~ (y -- x).

(** There is no arc inside [S]. *)
Definition arc_free (D : diGraph) (S : {set D}) : bool :=
  [forall u in S, [forall v in S, ~~ (u -- v)]].

(** Independence number. *)
Definition digraph_alpha (D : diGraph) : nat := \max_(S : {set D} | arc_free S) #|S|.

(** [X] dominates [D]: each vertex is in [X] or has an in-neighbour in [X]. *)
Definition out_dominating (D : diGraph) (X : {set D}) : bool :=
  [forall v : D, v \in NS[X]].

(** Domination number. *)
Definition out_domination_number (D : diGraph) : nat :=
  #|[arg min_(X < [set: D] | out_dominating X) #|X|]|.

(** ** Definitions specific to the conjecture *)

(** [D] has no directed triangle. *)
Definition directed_triangle_free (D : diGraph) : Prop :=
  forall x y z : D, x -- y -> y -- z -> ~~ (z -- x).

(** ** Statement *)

Definition AX_triangle_free_digraph_domination_polynomial_alpha : Prop :=
  exists l : nat, forall D : diGraph, oriented D -> directed_triangle_free D ->
    out_domination_number D <= digraph_alpha D ^ l.
