(** * Avoidability of the orientations of odd cycles

Christoph, Janzer, Petrova, Steiner, "Extending Thomassen's conjecture to directed graphs", 2025,
arXiv:2510.11311, Conjecture 6.1 (2510.11311__00).

A digraph F is avoidable if there is a function d : ℕ → ℕ such that, for every k, every digraph of
minimum out-degree at least d(k) contains an F-free subdigraph of minimum out-degree at least k.
Subdigraphs are not necessarily induced, and F-free means without a subdigraph isomorphic to F.

Conjecture: all orientations of odd cycles are avoidable.

Encoding.  Digraphs are those of GraphTheory ([diGraph]: a finite type of vertices with a boolean
relation [--]).  In the definition of avoidable, the digraph of minimum out-degree at least d(k) has
no loop, and may have digons, as in the paper.  It is nonempty, and so is its F-free subdigraph, as
the empty digraph has no minimum out-degree.  That subdigraph is a digraph [H] with an injective
homomorphism to [D] ([subdigraph H D]).  An orientation of the cycle on n vertices (n >= 3)
is a digraph without loop or digon whose underlying graph is isomorphic to it. *)

From GraphTheory Require Import preliminaries sgraph digraph.
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

(** The cycle on [n] vertices ([3 <= n] is meant). *)
Definition cycle_graph (n : nat) : sgraph :=
  sgraph_of_rel (fun i j : 'I_n => (val i).+1 %% n == val j).

(** ** Definitions copied from GraphLib/digraph.v *)

(** [D] is oriented: it has no digon, and no loop. *)
Definition oriented (D : diGraph) : Prop :=
  forall x y : D, x -- y -> ~~ (y -- x).

(** The underlying simple graph of [D]: arcs without direction, loops ignored. *)
Definition underlying (D : diGraph) : sgraph := sgraph_of_rel (@edge_rel D).

(** Out-degree. *)
Definition outdeg (D : diGraph) (v : D) : nat := #|N(v)|.

(** The minimum out-degree of [D] is at least [k]. *)
Definition min_outdeg_ge (D : diGraph) (k : nat) : Prop := forall v : D, (k <= outdeg v)%N.

(** [D] contains a (not necessarily induced) copy of [H]. *)
Definition subdigraph (H D : diGraph) : Prop :=
  exists f : H -> D, injective f /\ forall u v : H, u -- v -> f u -- f v.

(** [F] is avoidable: for some function [d], each loopless digraph of minimum out-degree at least
    [d k] contains a digraph of minimum out-degree at least [k] that contains no copy of [F]. *)
Definition avoidable (F : diGraph) : Prop :=
  exists d : nat -> nat,
    forall (k : nat) (D : diGraph),
      irreflexive (@edge_rel D) -> 0 < #|D| -> min_outdeg_ge D (d k) ->
      exists H : diGraph,
        [/\ 0 < #|H|, subdigraph H D, min_outdeg_ge H k & ~ subdigraph F H].

(** ** Statement *)

Definition AX_odd_cycle_orientations_avoidable : Prop :=
  forall (n : nat) (F : diGraph), odd n -> 2 < n ->
    oriented F -> inhabited (underlying F ≃ cycle_graph n) -> avoidable F.
