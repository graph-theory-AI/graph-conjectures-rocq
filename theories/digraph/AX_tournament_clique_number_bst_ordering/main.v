(** * Clique number of tournaments and BST-orderings

Aboulker, Aubian, Charbit, Lopes, "Clique number of tournaments", 2023, arXiv:2310.04265,
Conjecture 3.16 (2310.04265__04).

Given a total order ≺ on the vertices of a tournament T, the backedge graph T^≺ is the graph
on V(T) with an edge uv whenever u ≺ v and vu is an arc.  The clique number ω(T) of T is the
minimum over ≺ of the clique number of T^≺.

A BST-ordering of T is the left-to-right order of a binary search tree on V(T) in which, for every
vertex x, the left child of x and its descendants are in-neighbours of x, and the right child of x
and its descendants are out-neighbours of x.  In other words, it is obtained recursively: pick a
vertex x, put its in-neighbours to its left and its out-neighbours to its right, and order both
sides in the same way.

Conjecture 3.16: there exists a function f such that every tournament T has a BST-ordering ≺ with
ω(T^≺) <= f(ω(T)).

Encoding.  Tournaments are digraphs of GraphTheory ([diGraph]: a finite type of vertices with
a boolean relation [--]) satisfying the predicate [tournament].  Vertex orders are given by
permutations, composed with the canonical enumeration of the vertices.  BST-orderings are
described without trees: [bst_ordered p S] means that the order given by [p] is a BST-ordering of
the subtournament induced by S, where the root x is before its out-neighbours and after its
in-neighbours.  The empty tournament is included, and it has a BST-ordering. *)

From GraphTheory Require Import sgraph coloring digraph.
From mathcomp Require Import boot order perm.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/digraph.v *)

(** [D] is a tournament: it has no loop, and exactly one arc between any two distinct vertices. *)
Definition tournament (D : diGraph) : Prop :=
  irreflexive (@edge_rel D) /\ forall x y : D, (x != y) = (x -- y) (+) (y -- x).

(** [u] is before [v] in the order given by [p]. *)
Definition perm_lt (V : finType) (p : {perm V}) (u v : V) : bool :=
  enum_rank (p u) < enum_rank (p v).

Lemma perm_lt_irrefl (V : finType) (p : {perm V}) : irreflexive (perm_lt p).
Proof. by move=> u; rewrite /perm_lt ltnn. Qed.

(** There is an arc between [u] and [v] that goes backward in the order given by [p]. *)
Definition backedge_rel (D : diGraph) (p : {perm D}) : rel D :=
  [rel u v | perm_lt p u v && (v -- u) || perm_lt p v u && (u -- v)].

Lemma backedge_sym (D : diGraph) (p : {perm D}) : symmetric (backedge_rel p).
Proof. by move=> u v; rewrite /backedge_rel /= orbC. Qed.

Lemma backedge_irrefl (D : diGraph) (p : {perm D}) : irreflexive (backedge_rel p).
Proof. by move=> u; rewrite /backedge_rel /= perm_lt_irrefl. Qed.

(** The backedge graph of [D] in the order given by [p]. *)
Definition backedge_graph (D : diGraph) (p : {perm D}) : sgraph :=
  SGraph (backedge_sym p) (backedge_irrefl p).

(** The clique number of the digraph [D]: the minimum clique number of a backedge graph. *)
Definition diclique_number (D : diGraph) : nat :=
  ω([set: backedge_graph [arg min_(p < (1%g : {perm D})) ω([set: backedge_graph p])]]).

(** ** Definitions specific to the conjecture *)

(** The order given by [p] is a BST-ordering of the subtournament of [T] induced by [S]. *)
Inductive bst_ordered (T : diGraph) (p : {perm T}) : {set T} -> Prop :=
| bst_ordered_empty : bst_ordered p set0
| bst_ordered_root (S : {set T}) (x : T) :
    x \in S ->
    (forall y : T, y \in S -> y != x -> (y -- x) = perm_lt p y x) ->
    bst_ordered p [set y in S | y -- x] ->
    bst_ordered p [set y in S | x -- y] ->
    bst_ordered p S.

(** ** Statement *)

Definition AX_tournament_clique_number_bst_ordering : Prop :=
  exists f : nat -> nat, forall T : diGraph, tournament T ->
    exists p : {perm T},
      bst_ordered p [set: T] /\ ω([set: backedge_graph p]) <= f (diclique_number T).
