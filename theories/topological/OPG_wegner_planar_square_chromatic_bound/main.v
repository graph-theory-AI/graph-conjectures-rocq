(** * Wegner's conjecture on the square of planar graphs

Wegner, "Graphs with given diameter and a coloring problem", technical report, University of
Dortmund, 1977; Open Problem Garden, colouring_the_square_of_a_planar_graph.

The square of a graph G has the vertices of G, two of them being adjacent if their distance in G is
1 or 2.

Conjecture: let G be a planar graph of maximum degree Δ.  The chromatic number of its square is at
most

- 7 if Δ = 3,
- Δ + 5 if 4 <= Δ <= 7,
- ⌊3Δ/2⌋ + 1 if Δ >= 8.

Encoding.  Graphs are finite and simple.  Planarity is the absence of minors K_5 and K_3,3 (Wagner's
theorem).  The notation [n./2] is ⌊n/2⌋. *)

From GraphTheory Require Import preliminaries digraph sgraph coloring minor.
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

(** ** Definitions copied from GraphLib/topological.v *)

(** [G] is planar: it has no minor [K_5] or [K_3,3]. *)
Definition planar (G : sgraph) : Prop :=
  ~ minor G 'K_5 /\ ~ minor G (KB 3 3).

(** ** Statement *)

Definition OPG_wegner_planar_square_chromatic_bound : Prop :=
  forall G : sgraph,
    planar G ->
    [/\ Delta G = 3 -> χ([set: graph_power G 2]) <= 7,
        4 <= Delta G <= 7 -> χ([set: graph_power G 2]) <= Delta G + 5
      & 8 <= Delta G -> χ([set: graph_power G 2]) <= (3 * Delta G)./2 + 1].
