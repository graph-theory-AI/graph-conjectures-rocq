(** * Polynomial Nikiforov conjecture: every graph is viral

Nguyen, Scott, Seymour, "Induced subgraph density. IV. New graphs with the Erdős-Hajnal
property", arXiv:2307.06455, Conjecture 1.8 (2307.06455__00).

Let |G| be the number of vertices of G, and let ind_H(G) be the number of isomorphisms from H to
an induced subgraph of G.  A set S of vertices of G is ε-restricted if G[S] or its complement has
maximum degree at most ε|S|.

Conjecture 1.8 (every graph H is viral): for every graph H, there is d > 0 such that for every ε
with 0 < ε < 1/2 and every graph G with ind_H(G) <= (ε^d |G|)^|H|, there is an ε-restricted set of
at least ε^d |G| vertices of G.

Encoding.  H has at least one vertex (graphs are nonempty in the source; without this condition,
there is no restriction on G).  ε is a rational number a/b, d is a positive integer, and the
inequalities are multiplied by the denominators.  This is equivalent: d can be increased, and for
each graph G the case of a real number ε follows from that of its upper rational approximations. *)

From GraphTheory Require Import digraph sgraph.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

(** The maximum degree of [G] (0 if [G] is empty). *)
Definition Delta (G : sgraph) : nat := \max_(x : G) #|N(x)|.

(** ** Definitions copied from GraphLib/extremal.v *)

(** [X] is [a/b]-restricted: in [G] or in its complement, the maximum degree of the subgraph
    induced by [X] is at most [(a / b) |X|]. *)
Definition restricted_set (G : sgraph) (a b : nat) (X : {set G}) : Prop :=
  b * Delta (induced X) <= a * #|X| \/ b * Delta (@induced (compl G) X) <= a * #|X|.

(** ** Definitions specific to the conjecture *)

(** ind_[H]([G]): the number of injective maps that preserve adjacency and non-adjacency. *)
Definition induced_copy_count (G H : sgraph) : nat :=
  #|[set f : {ffun H -> G} |
      injectiveb f && [forall x : H, [forall y : H, (f x -- f y) == (x -- y)]]]|.

(** ** Statement *)

Definition AX_polynomial_nikiforov_all_graphs_viral : Prop :=
  forall H : sgraph, 0 < #|H| ->
    exists d : nat, 0 < d /\
      forall (a b : nat) (G : sgraph), 0 < a -> 2 * a < b ->
        b ^ (d * #|H|) * induced_copy_count G H <= (a ^ d * #|G|) ^ #|H| ->
        exists S : {set G}, restricted_set a b S /\ a ^ d * #|G| <= b ^ d * #|S|.
