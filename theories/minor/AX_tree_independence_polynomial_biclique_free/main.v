(** * Tree-independence number of K_{t,t}-free graphs of bounded induced matching treewidth

Alon, Milanič, Rzążewski, "Induced matching treewidth and tree-independence number, revisited",
arXiv:2511.03864, Question 5.2 (2511.03864__00).

The independence number of a tree decomposition of G is the maximum of α(G[B]) over its bags B, and
its induced matching number is the maximum size of an induced matching M of G such that some bag
contains at least one end of every edge of M.  The tree-independence number tree-α(G) and the
induced matching treewidth tree-μ(G) are the minimum of these numbers over the tree decompositions
of G.
A graph is H-free if it has no induced subgraph isomorphic to H.

Question 5.2: is it true that for every positive integer μ there exists a polynomial p_μ such that
every K_{t,t}-free graph G with tree-μ(G) <= μ satisfies tree-α(G) <= p_μ(t)?  The positive answer
is stated.

Encoding.  Polynomials have coefficients in nat, which is not a restriction for an upper bound: they
are lists of coefficients, and [horner_rec p t] is the value of [p] at t. *)

From GraphTheory Require Import digraph sgraph coloring treewidth.
From mathcomp Require Import boot algebra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

(** [G] has an induced subgraph isomorphic to [H]. *)
Definition has_induced_copy (G H : sgraph) : Prop := inhabited (H ⇀ G).

(** ** Definitions copied from GraphLib/minor.v *)

(** The tree-independence number of [G] is at most [k]. *)
Definition tree_independence_le (G : sgraph) (k : nat) : Prop :=
  exists (T : forest) (D : T -> {set G}), sdecomp T G D /\ forall t : T, α(D t) <= k.

(** [M] is an induced matching: the ends of distinct edges are distinct and non-adjacent. *)
Definition induced_matching (G : sgraph) (M : {set {set G}}) : Prop :=
  {subset M <= E(G)} /\
  forall (e f : {set G}) (x y : G),
    e \in M -> f \in M -> e != f -> x \in e -> y \in f -> (x != y) && ~~ (x -- y).

(** The induced matching treewidth of [G] is at most [m]: for some tree decomposition, each
    induced matching whose edges all meet a same bag has at most [m] edges. *)
Definition induced_matching_tw_le (G : sgraph) (m : nat) : Prop :=
  exists (T : forest) (D : T -> {set G}), sdecomp T G D /\
    forall M : {set {set G}},
      induced_matching M ->
      (exists t : T, forall e : {set G}, e \in M -> exists2 x : G, x \in e & x \in D t) ->
      #|M| <= m.

(** ** Statement *)

Definition AX_tree_independence_polynomial_biclique_free : Prop :=
  forall m : nat, 0 < m ->
    exists p : seq nat,
      forall (t : nat) (G : sgraph),
        ~ has_induced_copy G (KB t t) ->
        induced_matching_tw_le G m ->
        tree_independence_le G (horner_rec p t).
