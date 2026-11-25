(** * Pivot Gray codes of spanning trees

Bonamy, Hoffmann, Legrand-Duchesne, Rote, "A Gray code for arborescences of tournaments",
arXiv:2603.28614, Problem 1 (2603.28614__00).

A Gray code on the spanning trees of a graph G is a list of all its spanning trees, without
repetition, such that each tree except the first one is obtained from the previous one by
removing an edge and adding another edge.  It is a pivot Gray code if, moreover, the removed edge
and the added edge always share an endpoint.

Problem 1: does every graph G admit a pivot Gray code on its spanning trees?

The proposition states the positive answer.

Encoding.  The list is linear (not cyclic), and a spanning tree is given by its set of edges.  If G
is disconnected, then the list is empty. *)

From GraphTheory Require Import preliminaries digraph sgraph.
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

(** The relation given by a set of pairs. *)
Definition edge_set_rel (V : finType) (E : {set {set V}}) : rel V :=
  fun x y => [set x; y] \in E.

(** The graph on [V] with edge set [E]. *)
Definition sgraph_of_edges (V : finType) (E : {set {set V}}) : sgraph :=
  sgraph_of_rel (edge_set_rel E).

(** [T] is the edge set of a spanning tree of [G]. *)
Definition spanning_tree (G : sgraph) (T : {set {set G}}) : bool :=
  [&& T \subset E(G), is_forestb [set: sgraph_of_edges T]
    & connectedb [set: sgraph_of_edges T]].

(** ** Statement *)

Definition AX_spanning_trees_pivot_gray_code : Prop :=
  forall G : sgraph, exists s : seq {set {set G}},
    [/\ uniq s,
        forall T : {set {set G}}, T \in s <-> spanning_tree T
      & forall i : nat, i.+1 < size s ->
          exists e f : {set G},
            [/\ e \in nth set0 s i, f \notin nth set0 s i,
                nth set0 s i.+1 = (nth set0 s i :\ e) :|: [set f] & e :&: f != set0]].
