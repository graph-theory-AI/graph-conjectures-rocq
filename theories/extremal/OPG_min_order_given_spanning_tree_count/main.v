(** * Minimum order of a graph with a given number of spanning trees

Azarija, Škrekovski, "Euler's idoneal numbers and an inequality concerning minimal graphs with a
prescribed number of spanning trees"; Open Problem Garden,
minimal_graphs_with_a_prescribed_number_of_spanning_trees.

For n >= 3, let α(n) be the least k such that there is a simple graph with k vertices and exactly n
spanning trees.

Conjecture: α(n) = o(log n).

Encoding.  A spanning tree is given by its set of edges.  The statement is that for all positive
integers a and b, if n is large enough then α(n) < (a / b) log_2 n, that is 2^(b α(n)) < n^a. *)

From GraphTheory Require Import preliminaries digraph sgraph.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

(** [P n] holds for every sufficiently large [n]. *)
Definition eventually (P : nat -> Prop) : Prop :=
  exists N : nat, forall n : nat, N <= n -> P n.

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

(** ** Definitions copied from GraphLib/extremal.v *)

(** The number of spanning trees of [G]. *)
Definition spanning_tree_count (G : sgraph) : nat := #|[set T : {set {set G}} | spanning_tree T]|.

(** ** Definitions specific to the conjecture *)

(** [k] is the least number of vertices of a graph with exactly [n] spanning trees. *)
Definition min_order_spanning_trees (n k : nat) : Prop :=
  (exists G : sgraph, #|G| = k /\ spanning_tree_count G = n) /\
  (forall G : sgraph, spanning_tree_count G = n -> k <= #|G|).

(** ** Statement *)

Definition OPG_min_order_given_spanning_tree_count : Prop :=
  forall a b : nat, 0 < a -> 0 < b ->
    eventually (fun n => forall k : nat,
      3 <= n -> min_order_spanning_trees n k -> 2 ^ (b * k) < n ^ a).
