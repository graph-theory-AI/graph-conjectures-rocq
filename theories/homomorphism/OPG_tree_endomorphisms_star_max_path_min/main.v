(** * Number of endomorphisms of a tree

Lin; Open Problem Garden, extremal_problem_on_the_number_of_tree_endomorphism.

An endomorphism of a graph is a mapping from its vertex set to itself that maps adjacent vertices to
adjacent vertices.

Conjecture: among all trees with n vertices, the star has the most endomorphisms and the path has
the least.

Encoding.  The star with n vertices is the complete bipartite graph K_{1,n-1}.  It is assumed that
n >= 1: a tree is nonempty. *)

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

(** The path on [n] vertices. *)
Definition path_graph (n : nat) : sgraph := sgraph_of_rel (fun i j : 'I_n => (val i).+1 == val j).

(** ** Definitions copied from GraphLib/homomorphism.v *)

(** The number of homomorphisms from [H] to [G] (of endomorphisms of [G] if [H] is [G]). *)
Definition hom_count (H G : diGraph) : nat :=
  #|[set f : {ffun H -> G} | [forall x : H, [forall y : H, (x -- y) ==> (f x -- f y)]]]|.

(** ** Statement *)

Definition OPG_tree_endomorphisms_star_max_path_min : Prop :=
  forall (n : nat) (T : sgraph),
    0 < n -> is_tree [set: T] -> #|T| = n ->
    hom_count (path_graph n) (path_graph n) <= hom_count T T /\
    hom_count T T <= hom_count 'K_1,n.-1 'K_1,n.-1.
