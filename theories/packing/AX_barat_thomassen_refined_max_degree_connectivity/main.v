(** * Tree decompositions: edge-connectivity and maximum degree of the tree

Bensmail, Harutyunyan, Le, Thomassé, "Edge-partitioning a graph into paths: beyond the
Barát-Thomassen conjecture", arXiv:1507.08208, Conjecture 1.2 (1507.08208__00).

Graphs are finite and simple.  A T-decomposition of a graph G is a partition of E(G) into sets each
of which forms a copy of T (a subgraph isomorphic to T).  A graph is k-edge-connected if it has no
edge cut with fewer than k edges.  The maximum degree of T is denoted by Δ_T.

Conjecture: there is a function f such that, for every tree T, every f(Δ_T)-edge-connected graph
whose minimum degree is at least f(|E(T)|) and whose number of edges is divisible by |E(T)| has a
T-decomposition.

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

(** The maximum degree of [G] (0 if [G] is empty). *)
Definition Delta (G : sgraph) : nat := \max_(x : G) #|N(x)|.

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

(** ** Statement *)

Definition AX_barat_thomassen_refined_max_degree_connectivity : Prop :=
  exists f : nat -> nat,
    forall T G : sgraph,
      is_tree [set: T] -> 0 < #|E(T)| ->
      edge_connected G (f (Delta T)) ->
      min_degree_ge G (f #|E(T)|) ->
      #|E(T)| %| #|E(G)| ->
      exists D : seq {set {set G}}, edge_decomposition T D.
