(** * Independence number of a random set of vertices

Alon, Friedgut, Kalai, Kindler, "The success probability in Levine's hat problem, and independent
sets in graphs", arXiv:2208.06858, Conjecture 2.9 (2208.06858__04).

For a graph G on n vertices, let α(G) denote its independence number, and let α**(G) be the
expected value of α(G[W]) / n, where W is a uniformly random set of vertices (each vertex is in W
with probability 1/2, independently).  For α in (0,1/2), let ε**(α) be the infimum of
α(G)/n - α**(G) over all the graphs G such that α(G) >= αn.

Conjecture 2.9: ε**(α) > 0 for every α in (0,1/2).

Encoding.  The proposition states that for every rational α = a/b in (0,1/2) there is a rational
ε = e1/e2 > 0 such that α**(G) <= α(G)/n - ε for every nonempty graph G with α(G) >= αn.  Rational
numbers are enough because ε** is non-decreasing.  The expectation is an average over the 2^n sets
W, and the inequality is multiplied by the denominators.  [α(W)] is the maximum size of a stable
subset of W. *)

From GraphTheory Require Import digraph sgraph coloring.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions specific to the conjecture *)

(** The sum of the independence numbers of the subgraphs induced by all the sets of vertices,
    which is 2^n n α**(G). *)
Definition stable_sum (G : sgraph) : nat := \sum_(W : {set G}) α(W).

(** ** Statement *)

Definition AX_independence_ratio_binomial_subset_gap_positive : Prop :=
  forall a b : nat,
    0 < a -> 2 * a < b ->
    exists e1 e2 : nat,
      [/\ 0 < e1, 0 < e2 &
          forall G : sgraph,
            0 < #|G| -> a * #|G| <= b * α([set: G]) ->
            stable_sum G * e2 + e1 * (2 ^ #|G| * #|G|) <= e2 * (2 ^ #|G| * α([set: G]))].
