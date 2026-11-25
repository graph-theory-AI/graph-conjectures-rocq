(** * Edge-addition half of induced saturation for even cycles

Fan, S. Hajebi, S. Hajebi, Spirkl, "Halfway to induced saturation for even cycles",
arXiv:2505.24100, Question 1.7 (2505.24100__00).

A graph is H-free if it has no induced subgraph isomorphic to H.

Question: for every t >= 6, does there exist a graph G, with at least one pair of nonadjacent
vertices, that is C_(2t-2)-free, but such that adding any edge between two nonadjacent vertices
yields a graph with an induced C_(2t-2)?

The proposition states that the answer is yes.

Encoding.  Graphs are finite and simple. *)

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

(** [G] has an induced subgraph isomorphic to [H]. *)
Definition has_induced_copy (G H : sgraph) : Prop := inhabited (H ⇀ G).

(** [G] has no induced subgraph isomorphic to [H]. *)
Definition induced_free (G H : sgraph) : Prop := ~ has_induced_copy G H.

(** The cycle on [n] vertices ([3 <= n] is meant). *)
Definition cycle_graph (n : nat) : sgraph :=
  sgraph_of_rel (fun i j : 'I_n => (val i).+1 %% n == val j).

(** ** Statement *)

Definition AX_induced_even_cycle_saturation_edge_addition : Prop :=
  forall t : nat, 6 <= t ->
    exists G : sgraph,
      [/\ exists a b : G, a != b /\ ~~ (a -- b),
          induced_free G (cycle_graph (2 * t - 2))
        & forall a b : G, a != b -> ~~ (a -- b) ->
            has_induced_copy (add_edge a b) (cycle_graph (2 * t - 2))].
