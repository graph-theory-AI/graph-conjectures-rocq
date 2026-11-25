(** * Cuts of small chromatic number in sparse graphs

Aubian, Bonamy, Bourneuf, Fontaine, Picasarri-Arrieta, "On cuts of small chromatic number in sparse
graphs", arXiv:2510.01791, Conjecture 1.3 (2510.01791__00).

A cut of a graph G is a set X of vertices such that G - X is disconnected.  Let ℓ_k be the supremum
of the reals ℓ such that every sufficiently large graph (as a function of k and ℓ) of average degree
less than 2ℓ has a cut X with χ(G[X]) < k.

Conjecture 1.3: for every integer k and every graph G on at least k vertices, if
|E(G)| < k|V(G)| - k(k+1)/2, then G admits a cut X with χ(G[X]) < k.  In particular,
ℓ_k = k.

Encoding.  Graphs are finite and simple.  The inequality is multiplied by 2.  The case k <= 0, where
it never holds, is excluded.  The last sentence is not stated, as it follows from the first one: the
inequality ℓ_k <= k always holds, because of the join of a k-clique and an independent set. *)

From GraphTheory Require Import digraph sgraph connectivity coloring.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Statement *)

Definition AX_sparse_graph_cut_small_chromatic_number : Prop :=
  forall (k : nat) (G : sgraph),
    0 < k ->
    k <= #|G| ->
    2 * #|E(G)| < 2 * k * #|G| - k * k.+1 ->
    exists X : {set G}, disconnected (~: X) /\ χ([set: induced X]) < k.
