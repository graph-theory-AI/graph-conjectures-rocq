(** * Edge Reconstruction Conjecture

Harary; Bondy, "A graph reconstructor's manual", Surveys in Combinatorics (1991); Open Problem
Garden, edge_reconstruction_conjecture.

The edge-deck of a graph G is the multiset of the graphs G - e up to isomorphism, for all the edges
e of G.  G is edge-reconstructible if every graph with the same edge-deck as G is isomorphic to G.

Conjecture: every simple graph with at least 4 edges is edge-reconstructible.

Encoding.  Graphs are finite and simple.  Two graphs have the same edge-deck if there is a
bijection f between their edge sets such that G - e is isomorphic to H - f(e) for every edge e of
G.  [del_edges A] (GraphTheory) deletes the edges with both ends in the set A, hence only the edge e
when A = e. *)

From GraphTheory Require Import digraph sgraph.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/reconstruction.v *)

(** [G] and [H] have the same edge-deck. *)
Definition same_edge_deck (G H : sgraph) : Prop :=
  exists f : {e : {set G} | e \in E(G)} -> {e : {set H} | e \in E(H)},
    bijective f /\
    forall e : {e : {set G} | e \in E(G)},
      inhabited (del_edges (val e) ≃ del_edges (val (f e))).

(** [G] is reconstructible from its edge-deck. *)
Definition edge_reconstructible (G : sgraph) : Prop :=
  forall H : sgraph, same_edge_deck G H -> inhabited (G ≃ H).

(** ** Statement *)

Definition OPG_reconstruction_edge_deleted_subgraphs : Prop :=
  forall G : sgraph, 4 <= #|E(G)| -> edge_reconstructible G.
