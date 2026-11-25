(** * Oriented trees in n-chromatic digraphs (Burr's conjecture)

Burr, "Subtrees of directed graphs and hypergraphs", Congressus Numerantium 28 (1980);
Open Problem Garden, oriented_trees_in_n_chromatic_digraphs.

The chromatic number of a digraph is that of its underlying graph.  An oriented tree is an
orientation of a tree, and its order is its number of vertices.

Conjecture: every digraph with chromatic number at least 2k-2 contains every oriented tree of
order k as a subdigraph.

Encoding.  Digraphs are those of GraphTheory ([diGraph]): a finite type of vertices with a
boolean relation [--].  Digons and loops are allowed (loops are ignored in the underlying
graph).  Subdigraphs are not necessarily induced.  The case k = 1 is excluded, as the statement
would then fail for the digraph without vertices. *)

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

(** [D] is an orientation of a tree (with at least one vertex). *)
Definition oriented_tree (D : diGraph) : Prop :=
  [/\ (0 < #|D|)%N, oriented D & is_tree [set: underlying D]].

(** [D] contains a (not necessarily induced) copy of [H]. *)
Definition subdigraph (H D : diGraph) : Prop :=
  exists f : H -> D, injective f /\ forall u v : H, u -- v -> f u -- f v.

(** ** Statement *)

Definition OPG_chromatic_digraph_oriented_trees_2k : Prop :=
  forall (D : diGraph) (k : nat), 2 <= k -> 2 * k - 2 <= χ([set: underlying D]) ->
    forall T : diGraph, oriented_tree T -> #|T| = k -> subdigraph T D.
