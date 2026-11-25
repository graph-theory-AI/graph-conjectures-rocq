(** * Antidirected trees in digraphs

Addario-Berry, Havet, Linhares Sales, Reed, Thomassé, "Oriented trees in digraphs", Discrete
Mathematics 313 (2013); Open Problem Garden, antidirected_trees_in_digraphs.

An antidirected tree is an orientation of a tree in which every vertex has in-degree 0 or
out-degree 0.  The order of a tree is its number of vertices.

Conjecture: if a digraph D has more than (k-2)|V(D)| arcs, then D contains every antidirected
tree of order k.

Encoding.  Digraphs are those of GraphTheory ([diGraph]): a finite type of vertices with a
boolean relation [--], assumed irreflexive (no loop), as a loop counts as an arc.  Digons are
allowed, and they count as two arcs.  Subdigraphs are not necessarily induced.  The trivial case
k = 1 is excluded, so that the subtraction k - 2 is not truncated. *)

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

(** ** Definitions copied from GraphLib/digraph.v *)

(** [D] is oriented: it has no digon, and no loop. *)
Definition oriented (D : diGraph) : Prop :=
  forall x y : D, x -- y -> ~~ (y -- x).

(** The underlying simple graph of [D]: arcs without direction, loops ignored. *)
Definition underlying (D : diGraph) : sgraph := sgraph_of_rel (@edge_rel D).

(** [D] is an orientation of a tree (with at least one vertex). *)
Definition oriented_tree (D : diGraph) : Prop :=
  [/\ (0 < #|D|)%N, oriented D & is_tree [set: underlying D]].

(** Out-degree. *)
Definition outdeg (D : diGraph) (v : D) : nat := #|N(v)|.

(** In-degree. *)
Definition indeg (D : diGraph) (v : D) : nat := #|[set u | u -- v]|.

(** Each vertex is a source or a sink. *)
Definition antidirected (D : diGraph) : Prop := forall v : D, indeg v = 0 \/ outdeg v = 0.

(** [D] contains a (not necessarily induced) copy of [H]. *)
Definition subdigraph (H D : diGraph) : Prop :=
  exists f : H -> D, injective f /\ forall u v : H, u -- v -> f u -- f v.

(** ** Statement *)

Definition OPG_digraph_arcs_antidirected_trees : Prop :=
  forall (D : diGraph) (k : nat), 2 <= k -> irreflexive (@edge_rel D) ->
    (k - 2) * #|D| < num_edges D ->
    forall T : diGraph, oriented_tree T -> antidirected T -> #|T| = k -> subdigraph T D.
