(** * Halin's conjecture on hypomorphic infinite graphs

Halin; Bondy, Murty, "Graph Theory", Appendix A, problem 3.

Two graphs G and H are hypomorphic if there is a bijection φ from V(G) to V(H) such that G - v and
H - φ(v) are isomorphic for every vertex v of G.

Conjecture: if two infinite graphs are hypomorphic, then each is isomorphic to a subgraph of the
other.

Encoding.  Graphs are simple, with an arbitrary type of vertices and an adjacency relation in
[Prop].  Infinite means that there is an injection from the natural numbers to the vertices.
Subgraphs are not necessarily induced. *)

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

(** [G] is isomorphic to a subgraph of [H]. *)
Definition iembeds (G H : iGraph) : Prop :=
  exists f : ivertex G -> ivertex H,
    injective f /\ forall x y : ivertex G, iedge x y -> iedge (f x) (f y).

(** [G] minus [v] and [H] minus [w] are isomorphic. *)
Definition ivertex_deleted_iso (G H : iGraph) (v : ivertex G) (w : ivertex H) : Prop :=
  exists f : ivertex G -> ivertex H,
    [/\ forall x, x <> v -> f x <> w,
        forall x y, x <> v -> y <> v -> f x = f y -> x = y,
        forall y, y <> w -> exists x, x <> v /\ f x = y &
        forall x y, x <> v -> y <> v -> (iedge x y <-> iedge (f x) (f y))].

(** [G] and [H] are hypomorphic: for some bijection between their vertices, the subgraphs
    obtained by deleting corresponding vertices are isomorphic. *)
Definition ihypomorphic (G H : iGraph) : Prop :=
  exists phi : ivertex G -> ivertex H,
    bijective phi /\ forall v : ivertex G, @ivertex_deleted_iso G H v (phi v).

(** ** Statement *)

Definition BM_halin_reconstruction_infinite_hypomorphic_mutual_subgraph : Prop :=
  forall G H : iGraph,
    infinite_graph G -> infinite_graph H -> ihypomorphic G H -> iembeds G H /\ iembeds H G.
