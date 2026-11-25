(** * Excluding an ordered matching

Aboulker, Aubian, Charbit, Lopes, "Clique number of tournaments", arXiv:2310.04265, Conjecture 4.11
(2310.04265__06).

An ordered graph (G,<) is a graph with a total order on its vertices.  It is (M,<)-free if there is
no increasing map from M to G that preserves adjacency and non-adjacency.  A class of ordered graphs
is χ-bounded if, for some function f, χ(G) <= f(ω(G)) for every (G,<) in the class.

Conjecture 4.11: if (M,<) is an ordered graph of maximum degree 1, then the class of (M,<)-free
ordered graphs is χ-bounded.

Encoding.  The vertices are 0,...,n-1 with their usual order, without loss of generality.  The edges
are given by any relation, up to symmetry and loops.  M may have no edge (maximum degree at
most 1), a case that follows from Ramsey's theorem. *)

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

(** ** Definitions specific to the conjecture *)

(** The ordered graph of [M] is an induced ordered subgraph of that of [E]. *)
Definition ord_contains (m n : nat) (M : rel 'I_m) (E : rel 'I_n) : Prop :=
  exists phi : 'I_m -> 'I_n,
    (forall i j : 'I_m, i < j -> phi i < phi j) /\
    forall i j : 'I_m,
      @edge_rel (sgraph_of_rel M) i j = @edge_rel (sgraph_of_rel E) (phi i) (phi j).

(** The ordered graph of [M] has maximum degree at most 1. *)
Definition max_degree_one (m : nat) (M : rel 'I_m) : Prop :=
  forall i : sgraph_of_rel M, #|N(i)| <= 1.

(** ** Statement *)

Definition AX_ordered_graph_matching_free_chi_bounded : Prop :=
  forall (m : nat) (M : rel 'I_m), max_degree_one M ->
    exists f : nat -> nat, forall (n : nat) (E : rel 'I_n),
      ~ ord_contains M E -> χ([set: sgraph_of_rel E]) <= f (ω([set: sgraph_of_rel E])).
