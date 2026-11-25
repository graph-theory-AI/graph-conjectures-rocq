(** * Twin-width of the classes with polynomial expansion

Bonnet, Geniet, Kim, Thomassé, Watrigant, "Twin-width II: small classes", arXiv:2006.09877,
question following the Small Conjecture (2006.09877__01).

The twin-width of G is the minimum d such that G can be reduced to a single vertex by successive
contractions of two vertices, adjacent or not, with red degree at most d at each step.  After some
contractions, there is a red edge between two vertices when there are both edges and non-edges of
G between the sets of vertices contracted into them.  A class has bounded twin-width if some d
bounds the twin-width of all its graphs.

An r-shallow minor of G is a minor whose branch sets induce subgraphs of radius at most r.  A class
has polynomial expansion if there is a polynomial p such that |E(H)| <= p(r) |V(H)| for every
r >= 0 and every r-shallow minor H of a graph of the class.

Question: do classes with polynomial expansion have bounded twin-width?  The positive answer is
stated.

Encoding.  The polynomial has coefficients in nat, which is not a restriction for an upper bound:
it is the list [p] of its coefficients, by increasing degree, and [horner_rec p r] is its value at
r.  Classes of graphs are arbitrary predicates.  Contraction sequences are sequences of partitions
of the vertex set, where each step merges two parts; they end with at most one part, so that the
empty graph is included.  The definition of twin-width also applies to digraphs, which is why red
pairs are considered in both directions; for graphs, they are symmetric. *)

From GraphTheory Require Import digraph sgraph minor.
From mathcomp Require Import boot algebra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

(** The vertices of [G] at distance at most [k] from [x]. *)
Definition ball (G : sgraph) (k : nat) (x : G) : {set G} := iter k (@closed_neigh_set G) [set x].

(** ** Definitions copied from GraphLib/minor.v *)

(** [H] is a minor of [G] at depth [r]: the branch sets have radius at most [r]. *)
Definition shallow_minor (G H : sgraph) (r : nat) : Prop :=
  exists2 B : H -> {set G}, minor_rmap B &
    forall x : H, exists c : induced (B x), ball r c = [set: induced (B x)].

(** The class [C] has polynomial expansion: the edge density of its minors at depth [r] is
    bounded by a polynomial in [r] (given by the list [p] of its coefficients). *)
Definition polynomial_expansion (C : sgraph -> Prop) : Prop :=
  exists p : seq nat,
    forall G : sgraph, C G ->
      forall (r : nat) (H : sgraph),
        shallow_minor G H r -> #|E(H)| <= horner_rec p r * #|H|.

(** There are both edges and non-edges from [X] to [Y]. *)
Definition red_pair (G : diGraph) (X Y : {set G}) : bool :=
  [exists x in X, exists y in Y, x -- y] && [exists x in X, exists y in Y, ~~ (x -- y)].

(** The red degree of the part [X] of [P]. *)
Definition red_degree (G : diGraph) (P : {set {set G}}) (X : {set G}) : nat :=
  #|[set Y in P | (Y != X) && (red_pair X Y || red_pair Y X)]|.

(** The partition into singletons. *)
Definition singletons (G : diGraph) : {set {set G}} := [set [set x] | x : G].

(** [Q] is obtained from [P] by merging two parts. *)
Definition merge_parts (G : diGraph) (P Q : {set {set G}}) : bool :=
  [exists X in P, exists Y in P, (X != Y) && (Q == (X :|: Y) |: (P :\ X :\ Y))].

(** The twin-width of the graph or digraph [G] is at most [d]: some sequence of merges from the
    partition into singletons to a single part has red degrees at most [d]. *)
Definition twin_width_le (G : diGraph) (d : nat) : Prop :=
  exists s : seq {set {set G}},
    [/\ path (@merge_parts G) (singletons G) s,
        #|last (singletons G) s| <= 1 &
        forall P : {set {set G}},
          P \in (singletons G :: s) ->
          forall X : {set G}, X \in P -> red_degree P X <= d].

(** ** Statement *)

Definition AX_polynomial_expansion_bounded_twin_width : Prop :=
  forall C : sgraph -> Prop,
    polynomial_expansion C ->
    exists d : nat, forall G : sgraph, C G -> twin_width_le G d.
