(** * Erdős-Sós conjecture

Erdős, Sós; Bondy, Murty, "Graph Theory", Appendix A, problem 33.

Conjecture: every simple graph with n vertices and more than n(k-1)/2 edges contains every tree with
k edges.

Encoding.  The tree T is contained as a subgraph, not necessarily induced.  The inequality
m > n(k-1)/2 is written n k < 2 m + n.  For k = 0, it means that the graph is nonempty. *)

From GraphTheory Require Import digraph sgraph.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Statement *)

Definition BM_erdos_sos_trees_edge_bound : Prop :=
  forall (G T : sgraph) (k : nat),
    is_tree [set: T] -> #|E(T)| = k ->
    #|G| * k < 2 * #|E(G)| + #|G| ->
    subgraph T G.
