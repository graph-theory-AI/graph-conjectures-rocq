(** * Complete bipartite subgraphs of perfect graphs

Fox, "A bipartite analogue of Dilworth's theorem", Order 23 (2006); Open Problem Garden,
complete_bipartite_subgraphs_of_perfect_graphs.

A graph is perfect if each of its induced subgraphs has equal chromatic number and clique number.

Question: is it true that, for every perfect graph G on n vertices, either G or its complement has a
complete bipartite subgraph with parts A and B of size at least n^(1-o(1))?  What is stated is the
positive answer.

Encoding.  The bound n^(1-o(1)) means: for every exponent 1 - a/b with 0 < a < b, if n is large
enough (depending only on a and b), then |A| and |B| are at least n^(1-a/b), which is written
n^(b-a) <= |A|^b.  Disjointness of A and B follows from the fact that all pairs are adjacent. *)

From GraphTheory Require Import digraph sgraph wpgt.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

(** Every vertex of [A] is adjacent to every vertex of [B]. *)
Definition complete_between (G : sgraph) (A B : {set G}) : bool :=
  [forall a in A, [forall b in B, a -- b]].

(** ** Statement *)

Definition OPG_perfect_graph_large_complete_bipartite_subgraph : Prop :=
  forall a b : nat, 0 < a -> a < b ->
    exists N : nat, forall (G : sgraph) (n : nat),
      #|G| = n -> N <= n -> perfect [set: G] ->
      exists A B : {set G},
        (complete_between A B /\ n ^ (b - a) <= #|A| ^ b /\ n ^ (b - a) <= #|B| ^ b) \/
        (@complete_between (compl G) A B /\
           n ^ (b - a) <= #|A| ^ b /\ n ^ (b - a) <= #|B| ^ b).
