(** * Partitioning edge-connectivity

DeVos; Open Problem Garden, partitioning_edge_connectivity.

A graph is k-edge-connected if it remains connected when fewer than k edges are deleted.

Question: let G be an (a+b+2)-edge-connected graph.  Does there exist a partition {A,B} of E(G) such
that (V,A) is a-edge-connected and (V,B) is b-edge-connected?

The proposition states the positive answer.

Encoding.  Graphs are the finite multigraphs of GraphTheory.  Loops are allowed, but they play no
role, nor does the reference direction of the edges.  A graph with one vertex is k-edge-connected
for every k.  The parts A and B may be empty, and B is given as the complement of A. *)

From GraphTheory Require Import mgraph.
From GraphTheory Require Import digraph sgraph.
From GraphTheory Require skeleton.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

(** Multigraphs without labels. *)
Abbreviation mgraph := (graph unit unit).

(** ** Definitions copied from GraphLib/cycle.v *)

Section EdgeSets.
Variable G : mgraph.
Implicit Types (F S T : {set edge G}).

(** The spanning subgraph with edge set [T] is connected. *)
Definition spanning_connected T : Prop :=
  connected [set: skeleton.skeleton (remove_edges (~: T))].

(** The spanning subgraph with edge set [S] is [a]-edge-connected. *)
Definition spanning_edge_connected S (a : nat) : Prop :=
  forall F : {set edge G}, F \subset S -> #|F| < a -> spanning_connected (S :\: F).

End EdgeSets.

(** ** Statement *)

Definition OPG_edge_connectivity_partition_a_plus_b : Prop :=
  forall (a b : nat) (G : mgraph),
    spanning_edge_connected [set: edge G] (a + b + 2) ->
    exists A : {set edge G},
      spanning_edge_connected A a /\ spanning_edge_connected (~: A) b.
