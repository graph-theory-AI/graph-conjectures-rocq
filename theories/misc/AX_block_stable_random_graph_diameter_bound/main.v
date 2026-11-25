(** * Diameter of the block tree of a random graph from a block-stable class

McDiarmid, Scott, "Random graphs from a block-stable class", European Journal of Combinatorics
58 (2016), arXiv:1408.4257, conjecture stated with Theorem 1.2 (1408.4257__00).

A block of a graph is a maximal 2-connected subgraph, or the subgraph formed by a bridge, or an
isolated vertex.  A class of graphs closed under isomorphism is block-stable if a graph belongs
to it if and only if each of its blocks does.  The block tree BT(G) of a connected graph G is
the bipartite graph with a node for each vertex and a node for each block of G, where a vertex
and a block are adjacent if and only if the vertex is in the block.

The authors prove that, if R_n is a uniformly random connected graph on {1,...,n} from a
block-stable class, then BT(R_n) has diameter at most 5 √(n log n) with high probability (that
is with a probability that tends to 1, for the n such that the class has a connected graph on
n vertices).

Conjecture: the factor √(log n) can be replaced by any function tending to infinity.  That is,
for every block-stable class and every function f tending to infinity, BT(R_n) has diameter at
most f(n) √n with high probability.

Encoding.  A class of graphs is a boolean predicate.  A block is given by its vertex set: a
maximal set of vertices that induces a connected graph without cut vertex.  In the block tree,
the sets of vertices that are not blocks are additional isolated nodes; the diameter is the
maximum distance between two nodes of the same component.  Graphs on {0,...,n-1} are given by
their edge sets.  Probabilities are quotients of numbers of edge sets.  The function f has
integer values and √n is rounded up, which is equivalent as f is an arbitrary function tending
to infinity. *)

From GraphTheory Require Import preliminaries digraph sgraph.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

Lemma sqrt_ceil_ex (n : nat) : exists s : nat, n <= s ^ 2.
Proof. by exists n; rewrite expnS expn1; case: n => // m; rewrite leq_pmulr. Qed.

(** The ceiling of the square root of [n]: the least [s] such that [n <= s ^ 2]. *)
Definition sqrt_ceil (n : nat) : nat := ex_minn (sqrt_ceil_ex n).

(** [P n] holds for every sufficiently large [n]. *)
Definition eventually (P : nat -> Prop) : Prop :=
  exists N : nat, forall n : nat, N <= n -> P n.

(** [f] tends to infinity. *)
Definition tends_to_infinity (f : nat -> nat) : Prop :=
  forall b : nat, eventually (fun n => b <= f n).

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

(** The vertices of [G] at distance at most [k] from [x]. *)
Definition ball (G : sgraph) (k : nat) (x : G) : {set G} := iter k (@closed_neigh_set G) [set x].

Lemma graph_dist_ex (G : sgraph) (x y : G) :
  exists k : nat, (y \in ball k x) || (k == #|G|).
Proof. by exists #|G|; rewrite eqxx orbT. Qed.

(** The distance of [x] and [y] ([#|G|] if they are in different components). *)
Definition graph_dist (G : sgraph) (x y : G) : nat :=
  ex_minn (graph_dist_ex x y).

(** A class of graphs is closed under isomorphism. *)
Definition iso_closed (C : sgraph -> Prop) : Prop :=
  forall G H : sgraph, C G -> diso G H -> C H.

(** [B] is nonempty and induces a connected subgraph without cut vertex. *)
Definition no_cut_vertex (G : sgraph) (B : {set G}) : bool :=
  [&& B != set0, connectedb B & [forall v in B, connectedb (B :\ v)]].

(** [B] is a block: a maximal set that induces a connected subgraph without cut vertex. *)
Definition is_block (G : sgraph) (B : {set G}) : bool :=
  no_cut_vertex B &&
  [forall B' : {set G}, (B \subset B') && no_cut_vertex B' ==> (B' == B)].

(** The vertex [v] is in the block [B]. *)
Definition block_tree_rel (G : sgraph) : rel (G + {set G})%type :=
  fun p q => match p, q with
             | inl v, inr B => (v \in B) && is_block B
             | _, _ => false
             end.

(** The bipartite graph between vertices and blocks (a vertex and a block are adjacent if the
    vertex is in the block); the sets of vertices that are not blocks are isolated vertices. *)
Definition block_tree (G : sgraph) : sgraph := sgraph_of_rel (@block_tree_rel G).

(** ** Definitions specific to the conjecture *)

(** The distance of two vertices in the same component is at most [d]. *)
Definition diameter_le (T : sgraph) (d : nat) : bool :=
  [forall p : T, forall q : T, connect (--) p q ==> (graph_dist p q <= d)].

(** The class [A] is block-stable. *)
Definition block_stable (A : sgraph -> bool) : Prop :=
  iso_closed (fun G : sgraph => A G) /\
  forall G : sgraph, A G <-> (forall B : {set G}, is_block B -> A (induced B)).

(** [E] is the edge set of a connected graph on [0, ..., n-1] that belongs to the class [A]. *)
Definition connected_member (A : sgraph -> bool) (n : nat) (E : {set {set 'I_n}}) : bool :=
  [&& E \subset E('K_n), A (sgraph_of_edges E) & connectedb [set: sgraph_of_edges E]].

(** [P n] holds with high probability for the weights [w n], where only the [n] such that the
    sum of the weights is not 0 are considered. *)
Definition whp_where_defined
    (T : nat -> finType) (w : forall n : nat, T n -> nat) (P : forall n : nat, pred (T n)) : Prop :=
  forall a b : nat, 0 < a -> a <= b ->
    eventually (fun n =>
      0 < \sum_x w n x ->
      b * (\sum_(x | P n x) w n x) >= (b - a) * (\sum_x w n x)).

(** ** Statement *)

Definition AX_block_stable_random_graph_diameter_bound : Prop :=
  forall (A : sgraph -> bool) (f : nat -> nat),
    block_stable A ->
    tends_to_infinity f ->
    @whp_where_defined (fun n : nat => {set {set 'I_n}})
      (fun n E => nat_of_bool (connected_member A E))
      (fun n E => diameter_le (block_tree (sgraph_of_edges E)) (f n * sqrt_ceil n)).
