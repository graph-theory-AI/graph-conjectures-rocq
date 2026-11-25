(** * Almost all non-Hamiltonian cubic graphs have a bridge

Filar, Haythorpe, Nguyen, "A conjecture on the prevalence of cubic bridge graphs", Discuss. Math.
Graph Theory 30 (2010); Open Problem Garden,
almost_all_non_hamiltonian_3_regular_graphs_are_1_connected.

Let NH(n) be the number of non-Hamiltonian connected 3-regular graphs on 2n vertices, and NHB(n) the
number of those that have connectivity 1, that is, that have a bridge (an edge whose deletion
disconnects the graph).

Conjecture: NHB(n) / NH(n) tends to 1 as n tends to infinity.

Encoding.  Graphs are simple and counted up to isomorphism, as in the source: NH(n) and NHB(n) are
numbers of isomorphism classes of graphs with vertices 0, ..., 2n-1, given by their sets of edges.
They are restricted to connected graphs, as in the source; this is implicit in the Open Problem
Garden.  For a connected 3-regular graph, having connectivity 1 and having a bridge are equivalent.
The limit is expressed by: for all k >= 1, NHB(n) >= (1 - 1/k) NH(n) for every sufficiently large
n. *)

From GraphTheory Require Import preliminaries digraph sgraph connectivity.
From mathcomp Require Import boot fingroup perm.

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

(** [e] is a bridge: an edge whose ends are in different components when it is deleted. *)
Definition bridge (G : sgraph) (e : {set G}) : bool :=
  (e \in E(G)) &&
  [exists x in e, exists y in e, ~~ connect (del_edges_rel e) x y].

(** ** Definitions copied from GraphLib/hamiltonicity.v *)

(** [c] is a Hamiltonian cycle of [G]. *)
Definition hamiltonian_cycle (G : sgraph) (c : seq G) : bool :=
  ucycleb (--) c && (size c == #|G|).
Arguments hamiltonian_cycle : clear implicits.

(** ** Definitions specific to the conjecture *)

Section Counting.
Variable m : nat.
Implicit Types (E F : {set {set 'I_m}}) (X : {set {set {set 'I_m}}}).

(** The graphs with edge sets [E] and [F] are isomorphic. *)
Definition iso_edge_sets E F : bool :=
  [exists s : {perm 'I_m}, F == [set s @: (e : {set 'I_m}) | e in E]].

(** The number of isomorphism classes of the graphs with edge sets in [X]. *)
Definition iso_class_count X : nat := #|equivalence_partition iso_edge_sets X|.

(** [E] is the edge set of a connected 3-regular graph on [0, ..., m-1]. *)
Definition connected_cubic E : bool :=
  [&& E \subset E('K_m), connectedb [set: sgraph_of_edges E]
    & [forall v : sgraph_of_edges E, #|N(v)| == 3]].

(** The graph with edge set [E] has a Hamiltonian cycle. *)
Definition edges_hamiltonian E : bool :=
  [exists c : m.-tuple 'I_m, hamiltonian_cycle (sgraph_of_edges E) c].

(** The graph with edge set [E] has a bridge. *)
Definition edges_bridged E : bool := [exists e, @bridge (sgraph_of_edges E) e].

End Counting.

(** The number of non-Hamiltonian connected 3-regular graphs on [2n] vertices. *)
Definition NH (n : nat) : nat :=
  iso_class_count [set E : {set {set 'I_(2 * n)}} |
    connected_cubic E && ~~ edges_hamiltonian E].

(** The number of those that have a bridge. *)
Definition NHB (n : nat) : nat :=
  iso_class_count [set E : {set {set 'I_(2 * n)}} |
    [&& connected_cubic E, ~~ edges_hamiltonian E & edges_bridged E]].

(** ** Statement *)

Definition OPG_non_hamiltonian_cubic_almost_all_bridged : Prop :=
  forall k : nat, eventually (fun n => k * NH n <= k * NHB n + NH n).
