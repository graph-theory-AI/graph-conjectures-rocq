(** * Negative association in uniform forests

Pemantle, "Towards a theory of negative dependence", J. Math. Phys. 41 (2000); Open Problem Garden,
negative_association_in_uniform_forests.

Conjecture: let G be a finite graph, let e and f be two edges of G, and let F be the edge set of a
forest chosen uniformly at random among all forests of G.  Then P(e ∈ F | f ∈ F) <= P(e ∈ F).

Encoding.  The forests of G are the sets of edges without cycle (spanning subgraphs).  The edges e
and f are distinct, which is implicit: for e = f the left-hand side is 1.  The inequality is
multiplied by the number of forests and by the number of forests that contain f, which are positive.
Graphs are simple.  This is not a restriction, since the conjecture for simple graphs implies it for
multigraphs: loops are in no forest, the inequality is clear if e and f are parallel, and otherwise
replacing each other edge by three paths of length 2 with the same ends gives a simple graph with
the same joint distribution of e ∈ F and f ∈ F. *)

From GraphTheory Require Import preliminaries digraph sgraph.
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

(** The relation given by a set of pairs. *)
Definition edge_set_rel (V : finType) (E : {set {set V}}) : rel V :=
  fun x y => [set x; y] \in E.

(** The graph on [V] with edge set [E]. *)
Definition sgraph_of_edges (V : finType) (E : {set {set V}}) : sgraph :=
  sgraph_of_rel (edge_set_rel E).

(** ** Definitions specific to the conjecture *)

(** The edge sets of the forests of [G]. *)
Definition forests (G : sgraph) : {set {set {set G}}} :=
  [set F : {set {set G}} | (F \subset E(G)) && is_forestb [set: sgraph_of_edges F]].

(** ** Statement *)

Definition OPG_uniform_random_forest_negative_association : Prop :=
  forall (G : sgraph) (e f : {set G}),
    e \in E(G) -> f \in E(G) -> e != f ->
    #|[set F in forests G | (e \in F) && (f \in F)]| * #|forests G|
      <= #|[set F in forests G | e \in F]| * #|[set F in forests G | f \in F]|.
