(** * Heroic sets made of a clique and an oriented forest

Aboulker, Charbit, Naserasr, "Extension of Gyárfás-Sumner conjecture to digraphs", 2020,
arXiv:2009.13319, Conjecture 4.4 (2009.13319__02).

Digraphs have no loop.  The dichromatic number of a digraph is the minimum number of colours in a
colouring of its vertices such that no colour class contains a directed cycle.  A set of digraphs is
heroic if the digraphs without any induced subdigraph in this set have bounded dichromatic number.
An oriented forest is an orientation of a forest.

Conjecture 4.4: for every oriented forest F and every integer k, the set made of the digon, K_k and
F is heroic.  Here K_k stands for all its orientations.  In other words, the digraphs without digon,
whose underlying graph has no clique of size k, and without induced copy of F have bounded
dichromatic number.

Encoding.  Digraphs are those of GraphTheory ([diGraph]): a finite type of vertices with a boolean
relation [--], without loop or digon here ([oriented]). *)

From GraphTheory Require Import preliminaries sgraph coloring digraph.
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

(** ** Definitions copied from GraphLib/digraph.v *)

(** [D] is oriented: it has no digon, and no loop. *)
Definition oriented (D : diGraph) : Prop :=
  forall x y : D, x -- y -> ~~ (y -- x).

(** The underlying simple graph of [D]: arcs without direction, loops ignored. *)
Definition underlying (D : diGraph) : sgraph := sgraph_of_rel (@edge_rel D).

(** [D] has no directed cycle: no edge [u -- v] such that [v] reaches [u]
    (a loop or a digon is a directed cycle). *)
Definition acyclic (D : diGraph) : bool :=
  [forall u : D, forall v : D, (u -- v) ==> ~~ connect (--) v u].

(** The dichromatic number of [D] is at most [k]: the vertices can be coloured with [k]
    colours so that each colour class induces an acyclic digraph. *)
Definition dicolorable (D : diGraph) (k : nat) : Prop :=
  exists col : D -> 'I_k, forall i : 'I_k, acyclic (induced [set v | col v == i]).

(** The digraphs of the class [C] have a bounded dichromatic number. *)
Definition dichromatic_bounded (C : diGraph -> Prop) : Prop :=
  exists B : nat, forall D : diGraph, C D -> dicolorable D B.

(** ** Statement *)

Definition AX_heroic_sets_clique_oriented_forest : Prop :=
  forall (F : diGraph) (k : nat), oriented F -> is_forest [set: underlying F] ->
    dichromatic_bounded (fun D : diGraph =>
      [/\ oriented D, ω([set: underlying D]) < k & ~ inhabited (F ⇀ D)]).
