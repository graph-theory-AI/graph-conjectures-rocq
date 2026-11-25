(** * The Erdős–Lovász Tihany conjecture

Lovász; Bondy, Murty, "Graph Theory", Appendix A, problem 45.

A graph is k-chromatic if its chromatic number is k.

Conjecture: if G is a k-chromatic graph containing no k-clique, and k + 1 = k_1 + k_2 with
k_1, k_2 >= 2, then G has vertex-disjoint subgraphs G_1 and G_2 such that G_i is k_i-chromatic,
i = 1, 2.

Encoding.  Graphs are finite and simple.  The subgraphs G_1 and G_2 are induced by disjoint sets A
and B of vertices.  This is equivalent: deleting vertices one by one from a set of chromatic number
at least k_i gives a set of chromatic number exactly k_i. *)

From GraphTheory Require Import digraph sgraph coloring.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Statement *)

Definition BM_erdos_lovasz_tihany_disjoint_chromatic_split : Prop :=
  forall (G : sgraph) (k k1 k2 : nat),
    χ([set: G]) = k ->
    (forall S : {set G}, clique S -> #|S| < k) ->
    k + 1 = k1 + k2 -> 2 <= k1 -> 2 <= k2 ->
    exists A B : {set G},
      [/\ [disjoint A & B], χ(A) = k1 & χ(B) = k2].
