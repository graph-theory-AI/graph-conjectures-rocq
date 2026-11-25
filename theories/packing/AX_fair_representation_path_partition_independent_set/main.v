(** * Fair representation of a vertex partition of a path by an independent set

Aharoni, Alon, Berger, Chudnovsky, Kotlar, Loebl, Ziv, "Fair representation by independent sets",
arXiv:1611.03196, Conjecture 1.6 (1611.03196__00).

Conjecture: given a partition of the vertex set of a path into sets V_1, ..., V_m, there exist an
independent set S and integers b_i, i <= m, such that |S ∩ V_i| >= |V_i| / 2 - b_i for all i, and

- b_1 + ... + b_m <= m / 2,
- b_i <= 1 for all i <= m.

Encoding.  The sets V_i may be empty, which does not matter.  The integers b_i may be negative.  The
inequalities are multiplied by 2. *)

From GraphTheory Require Import preliminaries digraph sgraph dom.
From mathcomp Require Import boot order algebra.

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

(** ** Definitions specific to the conjecture *)

(** The sets [V i] (possibly empty) form a partition of the vertices of [G]. *)
Definition vertex_partition (G : sgraph) (m : nat) (V : 'I_m -> {set G}) : Prop :=
  (forall v : G, exists i : 'I_m, v \in V i) /\
  forall i j : 'I_m, i != j -> [disjoint V i & V j].

(** ** Statement *)

Definition AX_fair_representation_path_partition_independent_set : Prop :=
  forall (n m : nat) (V : 'I_m -> {set path_graph n}),
    vertex_partition V ->
    exists (S : {set path_graph n}) (b : 'I_m -> int),
      [/\ stable S,
          (forall i : 'I_m, #|V i|%:R <= 2 * (#|S :&: V i|%:R + b i))%R,
          (2 * \sum_(i : 'I_m) b i <= m%:R)%R
        & forall i : 'I_m, (b i <= 1)%R].
