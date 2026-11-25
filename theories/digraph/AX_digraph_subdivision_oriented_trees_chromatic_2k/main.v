(** * Subdivisions of oriented trees in digraphs of large chromatic number

Aboulker, Cohen, Havet, Lochet, Moura, Thomassé, "Subdivisions in digraphs of large out-degree or
large dichromatic number", 2016, arXiv:1610.00876, Conjecture 11 (1610.00876__03).

A subdivision of a digraph F is obtained by replacing the arcs of F by directed paths (internally
disjoint, with new internal vertices).  The chromatic number χ(D) of a digraph D is the one of its
underlying graph, and mader_χ(F) is the least integer m such that every digraph D with χ(D) >= m
contains a subdivision of F.  An oriented tree is an orientation of a tree, and its order is its
number of vertices.

Conjecture: if T is an oriented tree of order k, then mader_χ(T) <= 2k-2.

Encoding.  Digraphs are those of GraphTheory ([diGraph]: a finite type of vertices with a boolean
relation [--]).  In D, digons are allowed, and also loops, which is equivalent: they change neither
χ(D) nor the directed paths.  D has at least one vertex: this matters only for k = 1, as the bound
is then 0. *)

From GraphTheory Require Import preliminaries sgraph coloring digraph.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

Lemma sgraph_of_rel_sym (V : finType) (r : rel V) :
  symmetric (fun x y => (x != y) && sc r x y).
Proof. by move=> x y /=; rewrite eq_sym orbC. Qed.

Lemma sgraph_of_rel_irrefl (V : finType) (r : rel V) :
  irreflexive (fun x y => (x != y) && sc r x y).
Proof. by move=> x; rewrite eqxx. Qed.

(** The graph on [V] whose edges are given by [r], up to symmetry and loops. *)
Definition sgraph_of_rel (V : finType) (r : rel V) : sgraph :=
  SGraph (@sgraph_of_rel_sym V r) (@sgraph_of_rel_irrefl V r).

Section Sequences.
Variable T : finType.
Implicit Types (s : seq T) (x y : T).

(** The elements of [s] other than [x] and [y]. *)
Definition seq_interior x y s : {set T} := [set:: s] :\: [set x; y].

End Sequences.

(** ** Definitions copied from GraphLib/digraph.v *)

(** [D] is oriented: it has no digon, and no loop. *)
Definition oriented (D : diGraph) : Prop :=
  forall x y : D, x -- y -> ~~ (y -- x).

(** The underlying simple graph of [D]: arcs without direction, loops ignored. *)
Definition underlying (D : diGraph) : sgraph := sgraph_of_rel (@edge_rel D).

(** [D] is an orientation of a tree (with at least one vertex). *)
Definition oriented_tree (D : diGraph) : Prop :=
  [/\ (0 < #|D|)%N, oriented D & is_tree [set: underlying D]].

(** [D] contains a subdivision of [F]: distinct branch vertices, and, for each arc of [F], a
    directed path between the corresponding branch vertices; the interiors of these paths are
    pairwise disjoint and contain no branch vertex. *)
Definition contains_disubdivision (F D : diGraph) : Prop :=
  exists branch : F -> D,
    injective branch /\
    exists paths : F -> F -> seq D,
      (forall u v : F, u -- v ->
        [/\ (0 < size (paths u v))%N,
            upath (branch u) (branch v) (paths u v)
          & [disjoint seq_interior (branch u) (branch v) (branch u :: paths u v)
             & [set y | [exists x : F, branch x == y]]]]) /\
      (forall u v x y : F, u -- v -> x -- y ->
        ((u != x) || (v != y)) ->
        [disjoint seq_interior (branch u) (branch v) (branch u :: paths u v)
         & seq_interior (branch x) (branch y) (branch x :: paths x y)]).

(** ** Statement *)

Definition AX_digraph_subdivision_oriented_trees_chromatic_2k : Prop :=
  forall (T : diGraph) (k : nat), oriented_tree T -> #|T| = k ->
    forall D : diGraph, 0 < #|D| -> 2 * k - 2 <= χ([set: underlying D]) ->
      contains_disubdivision T D.
