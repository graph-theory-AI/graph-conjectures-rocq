(** * Barát-Thomassen conjecture

Barát, Thomassen, "Claw-decompositions and Tutte-orientations", Journal of Graph Theory 52 (2006);
Bondy, Murty, "Graph Theory", Appendix A, problem 11.

A decomposition of a graph G is a family of edge-disjoint subgraphs of G whose union is G.  A graph
is k-edge-connected if it has no edge cut with fewer than k edges.  The number of edges of T is
denoted by e(T).

Conjecture: for every tree T there exists a natural number k such that every simple
k-edge-connected graph whose number of edges is divisible by e(T) admits a decomposition into copies
of T.

Encoding.  Trees are nonempty.  A graph with at most one vertex is k-edge-connected for every k,
which does not matter, as it has no edge.  If T has only one vertex, the statement is trivial, as
only 0 is divisible by e(T) = 0.  A decomposition is the list of the edge sets of the copies.  A
copy of T is a subgraph isomorphic to T, not necessarily induced: the image of an injective map from
T to G that preserves adjacency. *)

From GraphTheory Require Import digraph sgraph.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

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

Definition BM_barat_thomassen_tree_decomposition_edge_connected : Prop :=
  forall T : sgraph,
    0 < #|T| -> is_tree [set: T] ->
    exists k : nat,
      forall G : sgraph,
        edge_connected G k ->
        #|E(T)| %| #|E(G)| ->
        exists D : seq {set {set G}}, edge_decomposition T D.
