(** * Avoidability of the digraphs with a height function

Christoph, Janzer, Petrova, Steiner, "Extending Thomassen's conjecture to directed graphs", 2025,
arXiv:2510.11311, Question 6.2 (2510.11311__01).

A digraph F is avoidable if there is a function d : ℕ → ℕ such that, for every k, every digraph of
minimum out-degree at least d(k) contains an F-free subdigraph of minimum out-degree at least k.
Subdigraphs are not necessarily induced, and F-free means without a subdigraph isomorphic to F.
A height function of a digraph F is a function h : V(F) → ℤ such that h(v) = h(u) + 1 for every
arc (u,v).

Question: are all digraphs which allow a height function not avoidable?  The proposition states
the positive answer.

Encoding.  Digraphs are those of GraphTheory ([diGraph]: a finite type of vertices with a boolean
relation [--]).  In the definition of avoidable, the digraph of minimum out-degree at least d(k) has
no loop, and may have digons, as in the paper.  It is nonempty, and so is its F-free subdigraph, as
the empty digraph has no minimum out-degree.  That subdigraph is a digraph [H] with an injective
homomorphism to [D] ([subdigraph H D]).  Height functions have values in ℕ, which is
equivalent on a finite digraph (subtract the minimum). *)

From GraphTheory Require Import digraph.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/digraph.v *)

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

(** ** Definitions specific to the conjecture *)

(** [F] allows a height function. *)
Definition has_height_function (F : diGraph) : Prop :=
  exists h : F -> nat, forall u v : F, u -- v -> h v = (h u).+1.

(** ** Statement *)

Definition AX_height_function_digraphs_not_avoidable : Prop :=
  forall F : diGraph, has_height_function F -> ~ avoidable F.
