(** * Tree-independence number and induced biclique number

Alon, Milanič, Rzążewski, "Induced matching treewidth and tree-independence number, revisited",
arXiv:2511.03864, Question 5.3 (2511.03864__01).

The independence number of a tree decomposition of G is the maximum of α(G[B]) over its bags B, and
its induced matching number is the maximum size of an induced matching M of G such that some bag
contains at least one end of every edge of M.  The tree-independence number tree-α(G) and the
induced matching treewidth tree-μ(G) are the minimum of these numbers over the tree decompositions
of G.
The induced biclique number of G is the largest t such that G contains an induced
subgraph isomorphic to K_{t,t}.

Question 5.3: is it true that for classes of graphs with bounded induced matching treewidth, the
tree-independence number is bounded from above by a polynomial function of the induced biclique
number?  The positive answer is stated.

Encoding.  It is enough to consider, for each m, the class of the graphs of induced matching
treewidth at most m.  The induced biclique number is a relation between G and t.
Polynomials have coefficients in nat, which is not a restriction for an upper bound: they
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

(** The induced biclique number of [G] is [t]: [t] is maximum such that [G] has an induced
    subgraph isomorphic to [K_t,t]. *)
Definition induced_biclique_number (G : sgraph) (t : nat) : Prop :=
  has_induced_copy G (KB t t) /\
  forall s : nat, has_induced_copy G (KB s s) -> s <= t.

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

Definition AX_tree_independence_polynomial_induced_biclique_number : Prop :=
  forall m : nat,
    exists p : seq nat,
      forall (G : sgraph) (t : nat),
        induced_matching_tw_le G m -> induced_biclique_number G t ->
        tree_independence_le G (horner_rec p t).
