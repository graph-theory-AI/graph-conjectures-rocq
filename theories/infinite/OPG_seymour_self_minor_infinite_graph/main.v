(** * Seymour's self-minor conjecture

Seymour; Open Problem Garden, seymours_self_minor_conjecture.

A graph H is a minor of a graph G if a graph isomorphic to H is obtained from G by deleting
vertices, deleting edges and contracting edges.  It is a proper minor if at least one such
operation is used.

Conjecture: every infinite graph is a proper minor of itself.

Encoding.  Graphs are simple, with an arbitrary type of vertices and an adjacency relation in
[Prop].  A minor is given by its branch sets: nonempty, connected and pairwise disjoint sets of
vertices of G, one for each vertex of H, such that some edge of G joins the branch sets of any two
adjacent vertices of H.  It is proper if some vertex of G is in no branch set (vertex deletion), or
some branch set has at least two vertices (edge contraction), or some edge of G joins the branch
sets of two vertices of H that are not adjacent (edge deletion).  Infinite means that there is an
injection from the natural numbers to the vertices. *)

From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/infinite.v *)

(** Simple graphs, possibly infinite. *)
Record iGraph := Build_iGraph {
  ivertex : Type;
  iedge : ivertex -> ivertex -> Prop;
  iedge_sym : forall x y, iedge x y -> iedge y x;
  iedge_irrefl : forall x, ~ iedge x x }.

(** [G] is infinite. *)
Definition infinite_graph (G : iGraph) : Prop :=
  exists f : nat -> ivertex G, injective f.

(** There is a walk with vertices in [P]. *)
Inductive ireach (G : iGraph) (P : ivertex G -> Prop) : ivertex G -> ivertex G -> Prop :=
  | ireach0 x : P x -> ireach P x x
  | ireachS x y z : ireach P x y -> iedge y z -> P z -> ireach P x z.

(** [P] induces a connected subgraph. *)
Definition iconnected_set (G : iGraph) (P : ivertex G -> Prop) : Prop :=
  forall x y, P x -> P y -> ireach P x y.

(** The branch sets [b h] show that [H] is a minor of [G]: they are nonempty, connected and
    pairwise disjoint, and there is an edge between the branch sets of adjacent vertices. *)
Definition iminor_model (G H : iGraph) (b : ivertex H -> ivertex G -> Prop) : Prop :=
  [/\ (forall h : ivertex H, exists x, b h x),
      (forall h : ivertex H, iconnected_set (b h)),
      (forall (h1 h2 : ivertex H) (x : ivertex G), b h1 x -> b h2 x -> h1 = h2)
    & (forall h1 h2 : ivertex H, iedge h1 h2 ->
         exists x y, b h1 x /\ b h2 y /\ iedge x y) ].

(** ** Definitions specific to the conjecture *)

(** The minor of [G] given by the branch sets [b] is obtained by deleting a vertex, contracting an
    edge or deleting an edge at least once. *)
Definition iproper_minor_model (G H : iGraph) (b : ivertex H -> ivertex G -> Prop) : Prop :=
  [\/ exists x : ivertex G, forall h : ivertex H, ~ b h x,
      exists (h : ivertex H) (x y : ivertex G), [/\ b h x, b h y & x <> y]
    | exists (h1 h2 : ivertex H) (x y : ivertex G),
        [/\ ~ iedge h1 h2, b h1 x, b h2 y & iedge x y] ].

(** [G] is a proper minor of itself. *)
Definition proper_self_minor (G : iGraph) : Prop :=
  exists b : ivertex G -> ivertex G -> Prop, iminor_model b /\ iproper_minor_model b.

(** ** Statement *)

Definition OPG_seymour_self_minor_infinite_graph : Prop :=
  forall G : iGraph, infinite_graph G -> proper_self_minor G.
