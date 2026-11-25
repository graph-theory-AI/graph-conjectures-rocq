(** * The linear arboricity conjecture

Akiyama, Exoo, Harary (1981), Hilton (1982); Bondy, Murty, "Graph Theory", Appendix A, problem 16.

A linear forest is a graph each of whose components is a path.  The linear arboricity la(G) of a
graph G is the least number of linear forests into which the edge set of G can be decomposed.

Conjecture: every simple k-regular graph G satisfies la(G) = ⌈(k+1)/2⌉.

Encoding.  Graphs have at least one vertex and k is positive, as the formula fails for graphs
without edges, whose linear arboricity is 0.  A decomposition of the edges into q linear forests is
a colouring of the edges with q colours, each of which forms a linear forest.  The colouring is
defined on all sets of vertices, but only its values on the edges matter. *)

From GraphTheory Require Import digraph sgraph.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

(** The ceiling of [a / b] (0 if [b = 0]). *)
Definition ceil_div (a b : nat) : nat := (a + b - 1) %/ b.

(** The maximum degree of [G] (0 if [G] is empty). *)
Definition Delta (G : sgraph) : nat := \max_(x : G) #|N(x)|.

(** Every vertex has degree [d]. *)
Definition regular (G : sgraph) (d : nat) : Prop := forall v : G, #|N(v)| = d.

Section DelEdgeSet.
Variables (G : sgraph) (F : {set {set G}}).

(** The edges of [G] that are not in [F]. *)
Definition del_edge_set_rel : rel G := [rel x y : G | (x -- y) && ([set x; y] \notin F)].

Lemma del_edge_set_sym : symmetric del_edge_set_rel.
Proof. by move=> x y; rewrite /del_edge_set_rel /= sg_sym setUC. Qed.

Lemma del_edge_set_irrefl : irreflexive del_edge_set_rel.
Proof. by move=> x; rewrite /del_edge_set_rel /= sg_irrefl. Qed.

(** [G] without the edges of [F]. *)
Definition del_edge_set : sgraph := SGraph del_edge_set_sym del_edge_set_irrefl.

End DelEdgeSet.

(** [G] is a disjoint union of paths. *)
Definition linear_forest (G : sgraph) : Prop := is_forest [set: G] /\ Delta G <= 2.

(** ** Definitions copied from GraphLib/chromatic.v *)

(** The spanning subgraph formed by the edges with colour in [p]. *)
Definition edge_color_class (G : sgraph) (C : eqType) (col : {set G} -> C) (p : pred C) : sgraph :=
  del_edge_set [set e : {set G} | ~~ p (col e)].

(** ** Definitions copied from GraphLib/cycle.v *)

(** The edges of [G] can be partitioned into [q] linear forests ([0 < q] is meant). *)
Definition linear_arboricity_le (G : sgraph) (q : nat) : Prop :=
  exists col : {set G} -> 'I_q, forall i : 'I_q, linear_forest (edge_color_class col (pred1 i)).

(** The linear arboricity of [G] is [q]. *)
Definition linear_arboricity (G : sgraph) (q : nat) : Prop :=
  linear_arboricity_le G q /\
  forall q' : nat, linear_arboricity_le G q' -> q <= q'.

(** ** Statement *)

Definition BM_linear_arboricity_regular_graphs : Prop :=
  forall (k : nat) (G : sgraph),
    0 < #|G| -> 0 < k -> regular G k -> linear_arboricity G (ceil_div (k + 1) 2).
