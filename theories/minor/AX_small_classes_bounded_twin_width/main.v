(** * The Small Conjecture

Bonnet, Geniet, Kim, Thomassé, Watrigant, "Twin-width II: small classes", arXiv:2006.09877, the
Small Conjecture (2006.09877__00).

The twin-width of G is the minimum d such that G can be reduced to a single vertex by successive
contractions of two vertices, adjacent or not, with red degree at most d at each step.  After some
contractions, there is a red edge between two vertices when there are both edges and non-edges of
G between the sets of vertices contracted into them.  A class has bounded twin-width if some d
bounds the twin-width of all its graphs.

A class of graphs is hereditary if it is closed under induced subgraphs.  It is small if there is
a constant c such that, for every n, it contains at most n! c^n graphs on the vertex set
{1,...,n}.

The Small Conjecture: every small hereditary class has bounded twin-width.

Encoding.  Classes of graphs are predicates, and hereditary classes are closed under isomorphism.
The labelled graphs on n vertices are given by their adjacency functions on pairs of elements of
['I_n].  As membership in the class is not assumed to be decidable, the bound n! c^n is required
for every set of adjacency functions of graphs of the class.  The constant c is in nat, which is
not a restriction.  Contraction sequences are sequences of partitions of the vertex set, where each
step merges two parts; they end with at most one part, so that the empty graph is included.  The
definition of twin-width also applies to digraphs, which is why red pairs are considered in both
directions; for graphs, they are symmetric. *)

From GraphTheory Require Import digraph sgraph.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

(** A class of graphs is closed under isomorphism. *)
Definition iso_closed (C : sgraph -> Prop) : Prop :=
  forall G H : sgraph, C G -> diso G H -> C H.

(** A class of graphs is closed under taking induced subgraphs on subsets of vertices. *)
Definition induced_closed (C : sgraph -> Prop) : Prop :=
  forall (G : sgraph) (S : {set G}), C G -> C (induced S).

(** A class of graphs is hereditary. *)
Definition hereditary_class (C : sgraph -> Prop) : Prop :=
  iso_closed C /\ induced_closed C.

(** ** Definitions copied from GraphLib/minor.v *)

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

(** ** Definitions specific to the conjecture *)

(** [f] is the adjacency function of [G], for some numbering of its vertices. *)
Definition represents (n : nat) (f : {ffun 'I_n * 'I_n -> bool}) (G : sgraph) : Prop :=
  exists h : 'I_n -> G, bijective h /\ forall x y : 'I_n, f (x, y) = (h x -- h y).

(** The class [C] is small: it has at most n! c^n labelled graphs on [n] vertices. *)
Definition small_class (C : sgraph -> Prop) : Prop :=
  exists c : nat,
    forall (n : nat) (F : {set {ffun 'I_n * 'I_n -> bool}}),
      (forall f : {ffun 'I_n * 'I_n -> bool},
         f \in F -> exists2 G : sgraph, C G & represents f G) ->
      #|F| <= n`! * c ^ n.

(** ** Statement *)

Definition AX_small_classes_bounded_twin_width : Prop :=
  forall C : sgraph -> Prop,
    hereditary_class C -> small_class C ->
    exists d : nat, forall G : sgraph, C G -> twin_width_le G d.
