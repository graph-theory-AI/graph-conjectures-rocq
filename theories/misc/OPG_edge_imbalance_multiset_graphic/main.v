(** * Imbalance conjecture

Kozerenko, "Graphs with graphic imbalance sequences"; Open Problem Garden, imbalance_conjecture.

The imbalance of an edge e = uv of a graph G is imb(e) = |deg(u) - deg(v)|, and M_G is the
multiset of the imbalances of the edges of G.  A multiset is graphic if it is the multiset of the
degrees of some graph.

Conjecture: if imb(e) > 0 for every edge e of G, then M_G is graphic.

Encoding.  Graphs are finite and simple.  M_G is a list, and graphic lists are considered up to
the order of their elements. *)

From GraphTheory Require Import digraph sgraph.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

(** The degrees of the vertices of [G]. *)
Definition degree_sequence (G : sgraph) : seq nat := [seq #|N(v)| | v : G].

Section Subdivision.
Variable G : sgraph.

(** The edges, with a fixed orientation. *)
Definition oriented_edge (p : G * G) : bool := (p.1 -- p.2) && (enum_rank p.1 < enum_rank p.2)%N.

End Subdivision.

(** The list [s] is graphic: it is, up to order, the list of the degrees of some graph. *)
Definition graphic (s : seq nat) : Prop :=
  exists H : sgraph, perm_eq s (degree_sequence H).

(** The edges, with a fixed orientation. *)
Definition oriented_edges (G : sgraph) : {set G * G} :=
  [set p : G * G | oriented_edge p].

(** ** Definitions specific to the conjecture *)

(** The imbalance of the edge [p]. *)
Definition imb (G : sgraph) (p : G * G) : nat :=
  (#|N(p.1)| - #|N(p.2)|) + (#|N(p.2)| - #|N(p.1)|).

(** The list of the imbalances of the edges of [G]. *)
Definition imbalances (G : sgraph) : seq nat := [seq imb p | p <- enum (oriented_edges G)].

(** ** Statement *)

Definition OPG_edge_imbalance_multiset_graphic : Prop :=
  forall G : sgraph,
    (forall p : G * G, p \in oriented_edges G -> 0 < imb p) ->
    graphic (imbalances G).
