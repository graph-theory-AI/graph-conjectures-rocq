(** * Strong edge colourings

Erdős, Nešetřil; Open Problem Garden, strong_edge_colouring_conjecture.

A strong edge colouring of a graph G is an edge colouring in which every colour class is an
induced matching: distinct edges of the same colour have no common end, and no end of one is
adjacent to an end of the other.  The strong chromatic index sχ'(G) is the minimum number of
colours of a strong edge colouring of G.

Conjecture: if G has maximum degree Δ, then sχ'(G) <= 5Δ²/4 if Δ is even, and
sχ'(G) <= (5Δ² - 2Δ + 1)/4 if Δ is odd.

Encoding.  Graphs are finite and simple.  The strong chromatic index is the chromatic number of the
square of the line graph.  The divisions are exact. *)

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

(** The maximum degree of [G] (0 if [G] is empty). *)
Definition Delta (G : sgraph) : nat := \max_(x : G) #|N(x)|.

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

(** ** Statement *)

Definition OPG_strong_edge_chromatic_delta_squared_bound : Prop :=
  forall G : sgraph,
    strong_chromatic_index G <=
      (if odd (Delta G)
       then (5 * (Delta G) ^ 2 - 2 * (Delta G) + 1) %/ 4
       else (5 * (Delta G) ^ 2) %/ 4).
