(** * A generalization of Vizing's theorem to hypergraphs

Rosenfeld; Open Problem Garden, a_generalization_of_vizings_theorem.

A hypergraph is simple if it has no repeated edges, and d-uniform if every edge has d vertices.

Conjecture: let H be a simple d-uniform hypergraph such that every set of d - 1 vertices is
contained in at most r edges.  Then there is a colouring of the edges with r + d - 1 colours such
that any two edges which share d - 1 vertices have distinct colours.

Encoding.  A simple hypergraph on a finite type of vertices is given by the set of its edges.  The
condition d >= 1 is implicit in the source: sets of d - 1 vertices are meaningless for d = 0.  The
colours are the natural numbers less than r + d - 1. *)

From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/hypergraph.v *)

Section Hypergraph.
Variable T : finType.
Implicit Types (E : {set {set T}}) (e : {set T}).

(** [E] is [k]-uniform: every edge has [k] vertices. *)
Definition hg_uniform E (k : nat) : Prop := forall e, e \in E -> #|e| = k.

End Hypergraph.

(** ** Statement *)

Definition OPG_uniform_hypergraph_vizing_edge_coloring : Prop :=
  forall (T : finType) (E : {set {set T}}) (d r : nat),
    1 <= d -> hg_uniform E d ->
    (forall S : {set T}, #|S| = d.-1 -> #|[set e in E | S \subset e]| <= r) ->
    exists c : {set T} -> nat,
      {in E, forall e, c e < r + d - 1} /\
      {in E &, forall e e' : {set T}, e != e' -> #|e :&: e'| = d.-1 -> c e != c e'}.
