(** * Triangle packing and triangle edge-transversal

Tuza, "A conjecture on triangles of graphs", Graphs Combin. 6 (1990), 373-380; Open Problem Garden,
triangle_packing_vs_triangle_edge_transversal.

Conjecture: if G has at most k edge-disjoint triangles, then there is a set of 2k edges whose
deletion destroys every triangle.

Encoding.  Graphs are finite and simple.  A triangle is given by its set of vertices.  "A set of 2k
edges" means: a set of at most 2k edges. *)

From GraphTheory Require Import digraph sgraph.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

(** [T] is a triangle: a clique on three vertices. *)
Definition triangle (G : sgraph) (T : {set G}) : Prop := clique T /\ #|T| = 3.

(** ** Definitions specific to the conjecture *)

(** The edges with both ends in [T]. *)
Definition edges_within (G : sgraph) (T : {set G}) : {set {set G}} :=
  [set e in E(G) | e \subset T].

(** [P] is a set of edge-disjoint triangles. *)
Definition triangle_packing (G : sgraph) (P : {set {set G}}) : Prop :=
  (forall T : {set G}, T \in P -> triangle T) /\
  {in P &, forall T1 T2 : {set G}, T1 != T2 -> [disjoint edges_within T1 & edges_within T2]}.

(** ** Statement *)

Definition OPG_tuza_triangle_packing_edge_transversal : Prop :=
  forall (k : nat) (G : sgraph),
    (forall P : {set {set G}}, triangle_packing P -> #|P| <= k) ->
    exists S : {set {set G}},
      [/\ S \subset E(G), #|S| <= 2 * k
        & forall T : {set G}, triangle T -> exists2 e : {set G}, e \in edges_within T & e \in S].
