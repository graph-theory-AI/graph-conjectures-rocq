(** * Colouring random subgraphs

Bukh; Open Problem Garden, coloring_random_subgraphs.

For a graph G and p in [0,1], G_p is the random spanning subgraph of G where each edge of G appears
independently with probability p.

Problem: does there exist a constant c > 0 such that E(χ(G_{1/2})) > c χ(G) / log χ(G) for every
graph G?  The proposition states the positive answer.

Encoding.  Graphs are finite and simple.  The expectation is the mean value of the chromatic number
over all spanning subgraphs of G, given by their sets of edges.  The graphs with χ(G) <= 1 are
excluded, as the logarithm must be positive.  The logarithm is in base 2 and rounded down, which
only changes c (χ(G) >= 2), and c is rational, which is not a restriction. *)

From GraphTheory Require Import preliminaries digraph sgraph coloring.
From mathcomp Require Import boot order algebra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.Theory GRing.Theory Num.Theory.

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

(** ** Definitions specific to the conjecture *)

(** The expectation of the chromatic number of G_{1/2}. *)
Definition expected_chi_half (G : sgraph) : rat :=
  ((\sum_(S : {set {set G}} | S \subset E(G)) (χ([set: sgraph_of_edges S]))%:Q)
    / (2 ^ #|E(G)|)%:Q)%R.

(** ** Statement *)

Definition OPG_random_half_subgraph_chromatic_lower_bound : Prop :=
  exists c : rat, (0 < c)%R /\
    forall G : sgraph, 2 <= χ([set: G]) ->
      (c * (χ([set: G]))%:Q / (trunc_log 2 (χ([set: G])))%:Q < expected_chi_half G)%R.
