(** * Coloring the union of degenerate graphs

Tarsi; R. Klein, "On the colorability of m-composed graphs", Discrete Math. 133 (1994); Open
Problem Garden, coloring_the_union_of_degenerate_graphs.

A graph is k-degenerate if every nonempty subgraph has a vertex of degree at most k.

Conjecture: the union of a 1-degenerate graph (a forest) and a 2-degenerate graph is
5-colourable.

Encoding.  The two graphs are finite, simple and given by relations r1 and r2, made symmetric and
irreflexive, on a common nonempty set of vertices V (adding isolated vertices to a graph does not
change its degeneracy).  Their edges may overlap. *)

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

(** The subgraph induced by [W] is [k]-degenerate: each nonempty subset [S] of [W] has a
    vertex with at most [k] neighbours in [S]. *)
Definition degenerate_on (G : sgraph) (W : {set G}) (k : nat) : Prop :=
  forall S : {set G}, S \subset W -> S != set0 -> exists x, (x \in S) /\ #|N(x) :&: S| <= k.
Arguments degenerate_on {G} W k.

(** [G] is [k]-degenerate. *)
Definition degenerate (G : sgraph) (k : nat) : Prop :=
  degenerate_on [set: G] k.

(** ** Statement *)

Definition OPG_forest_plus_2_degenerate_5_colorable : Prop :=
  forall (V : finType) (r1 r2 : rel V),
    0 < #|V| ->
    degenerate (sgraph_of_rel r1) 1 ->
    degenerate (sgraph_of_rel r2) 2 ->
    χ([set: sgraph_of_rel (fun x y => r1 x y || r2 x y)]) <= 5.
