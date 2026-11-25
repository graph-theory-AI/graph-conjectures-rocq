(** * Strong edge colourings of truncations of cubic graphs

Barát, Dvořák, Haxell, Kardoš, Lužar, Onderko, Rajník, Soták, Ulyanov, "Open problems of the 33rd
Workshop on Cycles and Colourings", arXiv:2511.02892, Problem 4.1 (2511.02892__03).

A strong edge colouring of a graph G is an edge colouring in which any two edges that are adjacent
or joined by an edge have different colours, that is, a proper colouring of the square of the line
graph of G.  The strong chromatic index χ'_s(G) is the minimum number of its colours.  A claw is
K_1,3, and a diamond is K_4 minus an edge.  The truncation T(G) of a cubic graph G is obtained by
replacing each vertex by a triangle.

Problem 4.1: is it true that every diamond-free claw-free cubic graph is strongly 6-edge-colourable?
In other words, is it true that χ'_s(T(G)) = 6 for every cubic graph G?

The proposition states the positive answer to the second question.

Encoding.  Graphs are finite and simple.  The graph G is nonempty, since χ'_s is 0 for the empty
graph.  The vertices of T(G) are the darts of G (the edges with an orientation): the darts leaving a
vertex form a triangle, and each dart is joined to the opposite one.  The first formulation also
covers the truncations of cubic multigraphs with parallel edges, for which 6 colours do not always
suffice: for instance, χ'_s is 9 for the triangular prism, which is the truncation of the multigraph
with two vertices and three parallel edges. *)

From GraphTheory Require Import preliminaries digraph sgraph coloring.
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

(** Every vertex has degree [d]. *)
Definition regular (G : sgraph) (d : nat) : Prop := forall v : G, #|N(v)| = d.

(** The vertices of [G] at distance at most [k] from [x]. *)
Definition ball (G : sgraph) (k : nat) (x : G) : {set G} := iter k (@closed_neigh_set G) [set x].

(** The [m]-th power of [G]: distinct vertices at distance at most [m] are adjacent. *)
Definition graph_power (G : sgraph) (m : nat) : sgraph :=
  sgraph_of_rel (fun x y : G => y \in ball m x).

Section SimpleLineGraph.
Variable G : sgraph.

(** The edges of [G]. *)
Definition simple_line_vertex : Type := {e : {set G} | e \in E(G)}.

(** Distinct edges with a common end. *)
Definition simple_line_rel : rel simple_line_vertex :=
  fun e f => (val e != val f) && (val e :&: val f != set0).

Lemma simple_line_sym : symmetric simple_line_rel.
Proof. by move=> e f; rewrite /simple_line_rel eq_sym setIC. Qed.

Lemma simple_line_irrefl : irreflexive simple_line_rel.
Proof. by move=> e; rewrite /simple_line_rel eqxx. Qed.

(** The line graph of the simple graph [G]. *)
Definition simple_line_graph : sgraph := SGraph simple_line_sym simple_line_irrefl.

End SimpleLineGraph.

(** ** Definitions copied from GraphLib/chromatic.v *)

(** The strong chromatic index of [G]: the chromatic number of the square of its line graph. *)
Definition strong_chromatic_index (G : sgraph) : nat :=
  χ([set: graph_power (simple_line_graph G) 2]).

(** ** Definitions copied from GraphLib/topological.v *)

Section Embedding.
Variable G : sgraph.

(** The darts of [G]: the edges with an orientation. *)
Definition dart : Type := {p : G * G | p.1 -- p.2}.

Lemma rev_dart_proof (d : dart) : (sval d).2 -- (sval d).1.
Proof. by rewrite sg_sym; exact: (svalP d). Qed.

(** The opposite dart. *)
Definition rev_dart (d : dart) : dart := exist _ ((sval d).2, (sval d).1) (rev_dart_proof d).

End Embedding.

(** The truncation of [G]: two darts are adjacent if they leave the same vertex or if they are
    opposite. *)
Definition truncation (G : sgraph) : sgraph :=
  sgraph_of_rel (fun d e : dart G => ((sval d).1 == (sval e).1) || (e == rev_dart d)).

(** ** Statement *)

Definition AX_cubic_truncation_strong_6_edge_coloring : Prop :=
  forall G : sgraph,
    0 < #|G| -> regular G 3 -> strong_chromatic_index (truncation G) = 6.
