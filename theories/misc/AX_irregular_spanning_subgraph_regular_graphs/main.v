(** * Irregular spanning subgraphs of regular graphs

Alon, Wei, "Irregular subgraphs", arXiv:2108.02685, Conjecture 1.1 (2108.02685__00).

For a graph H, let m(H,k) denote the number of vertices of degree k in H.

Conjecture 1.1: every d-regular graph G on n vertices has a spanning subgraph H such that
|m(H,k) - n/(d+1)| <= 2 for every k with 0 <= k <= d.

Encoding.  H is given by its set of edges, and the inequalities are multiplied by d+1. *)

From GraphTheory Require Import digraph sgraph.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

(** Every vertex has degree [d]. *)
Definition regular (G : sgraph) (d : nat) : Prop := forall v : G, #|N(v)| = d.

(** The number of members of [F] that contain [v]: the degree of [v] in the hypergraph [F], or
    in the spanning subgraph with edge set [F]. *)
Definition incidence_degree (T : finType) (F : {set {set T}}) (v : T) : nat :=
  #|[set e in F | v \in e]|.

(** The number of vertices of degree [k] in the spanning subgraph of [G] with edge set [F]. *)
Definition degree_class_size (G : sgraph) (F : {set {set G}}) (k : nat) : nat :=
  #|[set v : G | incidence_degree F v == k]|.

(** ** Definitions specific to the conjecture *)

(** |m(H,k) - n/(d+1)| <= 2, where H has edge set [F]. *)
Definition close_to_uniform_degree_class
    (G : sgraph) (d : nat) (F : {set {set G}}) (k : nat) : Prop :=
  let m := degree_class_size F k in
  d.+1 * m <= #|G| + 2 * d.+1 /\ #|G| <= d.+1 * (m + 2).

(** ** Statement *)

Definition AX_irregular_spanning_subgraph_regular_graphs : Prop :=
  forall (d : nat) (G : sgraph),
    regular G d ->
    exists F : {set {set G}},
      F \subset E(G) /\
      forall k : nat, k <= d -> close_to_uniform_degree_class d F k.
