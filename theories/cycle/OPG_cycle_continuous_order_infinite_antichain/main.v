(** * Antichains in the cycle continuous order

DeVos; Open Problem Garden, antichains_in_the_cycle_continuous_order.

The (binary) cycle space of a graph G is the set of the sets of edges C such that every vertex is
in an even number of edges of C.  A map f : E(G) -> E(H) is cycle-continuous if the preimage of
every element of the cycle space of H is in the cycle space of G.

Problem: does there exist an infinite set of graphs {G_1, G_2, ...} such that there is no
cycle-continuous map between G_i and G_j whenever i <> j?

The proposition states the positive answer: there are such graphs.

Encoding.  Graphs are finite and simple, with at least one edge.  This is not restrictive: there
are cycle-continuous maps in both directions between a graph and any of its subdivisions, and a
graph without edges has a cycle-continuous map to every graph.  Edges are sets of two vertices,
and maps between edges are maps between sets of vertices that map edges to edges.  The pairs (i,j)
are ordered: there is no cycle-continuous map in either direction. *)

From GraphTheory Require Import digraph sgraph.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

(** The number of members of [F] that contain [v]: the degree of [v] in the hypergraph [F], or
    in the spanning subgraph with edge set [F]. *)
Definition incidence_degree (T : finType) (F : {set {set T}}) (v : T) : nat :=
  #|[set e in F | v \in e]|.

(** ** Definitions copied from GraphLib/cycle.v *)

(** [C] is in the cycle space of [G]: a set of edges with even degrees. *)
Definition in_cycle_space (G : sgraph) (C : {set {set G}}) : Prop :=
  C \subset E(G) /\
  (forall v : G, ~~ odd (incidence_degree C v)).

(** [f] is a cycle-continuous map: it maps the edges of [G] to edges of [H], and the preimages of
    the elements of the cycle space are in the cycle space. *)
Definition cycle_continuous (G H : sgraph) (f : {set G} -> {set H}) : Prop :=
  (forall e : {set G}, e \in E(G) -> f e \in E(H)) /\
  (forall C : {set {set H}}, in_cycle_space C ->
     in_cycle_space [set e in E(G) | f e \in C]).

(** ** Statement *)

Definition OPG_cycle_continuous_order_infinite_antichain : Prop :=
  exists Gs : nat -> sgraph,
    (forall i : nat, E(Gs i) != set0) /\
    (forall i j : nat, i <> j ->
       ~ exists f : {set Gs i} -> {set Gs j}, cycle_continuous f).
