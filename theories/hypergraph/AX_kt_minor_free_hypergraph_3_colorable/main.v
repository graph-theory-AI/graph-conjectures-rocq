(** * 3-colourability of K_3-minor-free hypergraphs

Steiner, "Coloring hypergraphs with excluded minors", arXiv:2206.13635, Problem 1 (2206.13635__01).

A hypergraph H has a K_t minor if there are t disjoint nonempty sets of vertices B_1, ..., B_t such
that each B_i is connected (any two of its vertices are joined by a walk in the edges contained in
B_i) and, for all i <> j, some edge is contained in B_i ∪ B_j and meets both.  Equivalently, K_t can
be obtained from H by deleting vertices, deleting edges and contracting edges (the edges contained
in a contracted edge are deleted).  A colouring of the vertices is proper if no edge is
monochromatic, and H is 3-colourable if it has a proper colouring with 3 colours.

Problem 1: is every hypergraph without K_3 minor 3-colourable?

The proposition states that the answer is yes, as predicted by a conjecture of the author.

Encoding.  Hypergraphs are finite and every edge has at least two vertices, as in the source. *)

From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/hypergraph.v *)

Section Hypergraph.
Variable T : finType.
Implicit Types (E : {set {set T}}) (e S : {set T}).

(** Every edge has at least two vertices. *)
Definition hg_loopless E : Prop := forall e, e \in E -> 2 <= #|e|.

(** The edges contained in [S]. *)
Definition hg_restrict E S : {set {set T}} := [set e in E | e \subset S].

(** [u] and [v] are in a common edge. *)
Definition hg_adjacent E : rel T := fun u v => [exists e in E, (u \in e) && (v \in e)].

(** Any two vertices of [S] are joined by a walk in the edges contained in [S]. *)
Definition hg_connected_on E S : Prop :=
  forall u v : T, u \in S -> v \in S -> connect (hg_adjacent (hg_restrict E S)) u v.

(** [col] is a proper (weak) colouring: no edge is monochromatic. *)
Definition hg_proper_coloring (C : finType) E (col : T -> C) : Prop :=
  forall e, e \in E -> exists x y, [/\ x \in e, y \in e & col x != col y].

(** [E] has a proper colouring with [m] colours. *)
Definition hg_colorable E (m : nat) : Prop :=
  exists col : T -> 'I_m, hg_proper_coloring E col.

(** The branch sets [B] of a minor [K_t]: they are nonempty, pairwise disjoint and induce
    connected hypergraphs and, for any two of them, some edge meets both and is contained in
    their union. *)
Definition hg_clique_minor_model E (t : nat) (B : 'I_t -> {set T}) : Prop :=
  [/\ forall h, B h != set0,
      forall h h', h != h' -> [disjoint B h & B h'],
      forall h, hg_connected_on E (B h) &
      forall h h' : 'I_t, h != h' ->
        exists e, [/\ e \in E, e \subset B h :|: B h',
                      e :&: B h != set0 & e :&: B h' != set0]].

(** [E] has a minor [K_t]. *)
Definition hg_has_clique_minor E (t : nat) : Prop :=
  exists B : 'I_t -> {set T}, hg_clique_minor_model E B.

End Hypergraph.

(** ** Statement *)

Definition AX_kt_minor_free_hypergraph_3_colorable : Prop :=
  forall (T : finType) (E : {set {set T}}),
    hg_loopless E -> ~ hg_has_clique_minor E 3 -> hg_colorable E 3.
