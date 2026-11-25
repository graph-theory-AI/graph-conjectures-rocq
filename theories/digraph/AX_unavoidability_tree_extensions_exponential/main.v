(** * Unavoidability of the k-extensions of oriented trees

Aboulker, Havet, Lochet, Lopes, Picasarri-Arrieta, Rambaud, "Blow-ups and extensions of trees in
tournaments", 2024, arXiv:2410.23566, Conjecture 10 (2410.23566__04).

A digraph D is p-unavoidable if every tournament on p vertices contains D as a (not necessarily
induced) subdigraph.  Let k be a positive integer.  An acyclic digraph D is a k-extension of A if
D - S = A for some set S of k vertices.

Conjecture 10: there is an absolute constant C such that, for every integer k, every k-extension of
an oriented tree of order n is C^k(2n-2)-unavoidable.

Encoding.  Digraphs are those of GraphTheory ([diGraph]: a finite type of vertices with a boolean
relation [--]); D - S = A is read up to isomorphism.  The guard k > 0 is part of the definition of
the k-extensions (k = 0 would give Sumner's conjecture exactly).  The guard n > 1, as in Sumner's
conjecture, is needed: the bound is 0 for n = 1.  The constant C is a natural number, without loss
of generality as N-unavoidable digraphs are (N+1)-unavoidable. *)

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

(** [D] is a tournament: it has no loop, and exactly one arc between any two distinct vertices. *)
Definition tournament (D : diGraph) : Prop :=
  irreflexive (@edge_rel D) /\ forall x y : D, (x != y) = (x -- y) (+) (y -- x).

(** The underlying simple graph of [D]: arcs without direction, loops ignored. *)
Definition underlying (D : diGraph) : sgraph := sgraph_of_rel (@edge_rel D).

(** [D] is an orientation of a tree (with at least one vertex). *)
Definition oriented_tree (D : diGraph) : Prop :=
  [/\ (0 < #|D|)%N, oriented D & is_tree [set: underlying D]].

(** [D] has no directed cycle: no edge [u -- v] such that [v] reaches [u]
    (a loop or a digon is a directed cycle). *)
Definition acyclic (D : diGraph) : bool :=
  [forall u : D, forall v : D, (u -- v) ==> ~~ connect (--) v u].

(** [D] contains a (not necessarily induced) copy of [H]. *)
Definition subdigraph (H D : diGraph) : Prop :=
  exists f : H -> D, injective f /\ forall u v : H, u -- v -> f u -- f v.

(** Each tournament on [N] vertices contains [D]. *)
Definition tournament_unavoidable (D : diGraph) (N : nat) : Prop :=
  forall T : diGraph, tournament T -> #|T| = N -> subdigraph D T.

(** The acyclic digraph [D] is a [k]-extension of [A]: the deletion of some [k] vertices gives
    [A]. *)
Definition k_extension (k : nat) (A D : diGraph) : Prop :=
  acyclic D /\ exists S : {set D}, #|S| = k /\ inhabited (induced (~: S) ≃ A).

(** ** Statement *)

Definition AX_unavoidability_tree_extensions_exponential : Prop :=
  exists C : nat, forall (k : nat) (A D : diGraph),
    0 < k -> oriented_tree A -> 1 < #|A| -> k_extension k A D ->
    tournament_unavoidable D (C ^ k * (2 * #|A| - 2)).
