(** * Tree decompositions: edge-connectivity and number of leaves of the tree

Klimošová, Thomassé, "Edge-partitioning 3-edge-connected graphs into paths", arXiv:1907.11600,
Conjecture 5 (1907.11600__00).

Graphs are finite and simple.  A T-decomposition of a graph G is a partition of E(G) into sets each
of which forms a copy of T (a subgraph isomorphic to T).  A graph is k-edge-connected if it has no
edge cut with fewer than k edges.

Conjecture: there is a function f such that, for every tree T with m leaves, every
f(m)-edge-connected graph whose minimum degree is at least f(|E(T)|) and whose number of edges is
divisible by |E(T)| has a T-decomposition.

Encoding.  Trees are nonempty, and the tree T is assumed to have at least one edge, as otherwise
there is nothing to decompose into.  A decomposition is the list of the edge sets of the copies.  A
copy of T is the image of an injective map from T to G that preserves adjacency.  A graph with at
most one vertex is k-edge-connected for every k, which does not matter, as it has no edge. *)

From GraphTheory Require Import digraph sgraph.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

(** Every vertex has degree at least [d] (true if [G] is empty). *)
Definition min_degree_ge (G : sgraph) (d : nat) : Prop := forall v : G, d <= #|N(v)|.

(** [A] is the edge set of a copy of [T] in [G] (as a subgraph). *)
Definition embedded_edge_copy (G T : sgraph) (A : {set {set G}}) : Prop :=
  exists f : T -> G,
    [/\ injective f,
        (forall x y : T, x -- y -> f x -- f y)
      & A = [set f @: (e : {set T}) | e in E(T)]].
Arguments embedded_edge_copy {G} T A.

(** The edges of [G] are partitioned by the copies of [T] whose edge sets are listed in [D]. *)
Definition edge_decomposition (G T : sgraph) (D : seq {set {set G}}) : Prop :=
  (forall A, A \in D -> embedded_edge_copy T A) /\
  (forall e : {set G},
     count (fun A : {set {set G}} => e \in A) D = ((e \in E(G)) : nat)).
Arguments edge_decomposition {G} T D.

(** The edges with exactly one end in [S]. *)
Definition cut_edges (G : sgraph) (S : {set G}) : {set {set G}} :=
  [set e in E(G) | (e :&: S != set0) && (e :&: (~: S) != set0)].

(** [G] is [k]-edge-connected: every cut has at least [k] edges (always true if [G] has at most
    one vertex). *)
Definition edge_connected (G : sgraph) (k : nat) : Prop :=
  forall S : {set G}, S != set0 -> S != [set: G] -> k <= #|cut_edges S|.

(** ** Definitions specific to the conjecture *)

(** The number of leaves (vertices of degree 1). *)
Definition leaf_count (T : sgraph) : nat := #|[set v : T | #|N(v)| == 1]|.

(** ** Statement *)

Definition AX_tree_decomposition_edge_connectivity_leaf_count : Prop :=
  exists f : nat -> nat,
    forall T G : sgraph,
      is_tree [set: T] -> 0 < #|E(T)| ->
      edge_connected G (f (leaf_count T)) ->
      min_degree_ge G (f #|E(T)|) ->
      #|E(T)| %| #|E(G)| ->
      exists D : seq {set {set G}}, edge_decomposition T D.
