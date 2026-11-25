(** * Eulerian-avoidability of the orientations of C_4

Christoph, Janzer, Petrova, Steiner, "Extending Thomassen's conjecture to directed graphs", 2025,
arXiv:2510.11311, Question 6.4 (2510.11311__04).

A digraph is Eulerian if every vertex has the same in-degree as out-degree.  A digraph F is
Eulerian-avoidable if there is a function d such that, for every k, every Eulerian digraph with
minimum out-degree at least d(k) contains a subdigraph with minimum out-degree at least k and
without copy of F.

Question 6.4: is every orientation of C_4 Eulerian-avoidable?  The proposition states the positive
answer.

Encoding.  Digraphs are those of GraphTheory ([diGraph]): a finite type of vertices with a boolean
relation [--].  Digons are allowed in Eulerian digraphs.  Loops are allowed too, which is
equivalent, as they change the out-degrees by at most one.  Eulerian digraphs and their subdigraphs
have at least one vertex (minimum out-degrees are meaningless otherwise).  Subdigraphs and copies of
F are not necessarily induced. *)

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

(** In-degree. *)
Definition indeg (D : diGraph) (v : D) : nat := #|[set u | u -- v]|.

(** The minimum out-degree of [D] is at least [k]. *)
Definition min_outdeg_ge (D : diGraph) (k : nat) : Prop := forall v : D, (k <= outdeg v)%N.

(** Each vertex has as many in-neighbours as out-neighbours (such a digraph is also called
    eulerian, connected or not). *)
Definition balanced_digraph (D : diGraph) : bool := [forall v : D, indeg v == outdeg v].

(** [D] contains a (not necessarily induced) copy of [H]. *)
Definition subdigraph (H D : diGraph) : Prop :=
  exists f : H -> D, injective f /\ forall u v : H, u -- v -> f u -- f v.

(** ** Definitions specific to the conjecture *)

(** [F] is Eulerian-avoidable: the Eulerian digraphs of large minimum out-degree have [F]-free
    subdigraphs of large minimum out-degree. *)
Definition eulerian_avoidable (F : diGraph) : Prop :=
  exists d : nat -> nat, forall (k : nat) (D : diGraph),
    balanced_digraph D -> 0 < #|D| -> min_outdeg_ge D (d k) ->
    exists H : diGraph, [/\ 0 < #|H|, subdigraph H D, min_outdeg_ge H k & ~ subdigraph F H].

(** ** Statement *)

Definition AX_c4_orientations_eulerian_avoidable : Prop :=
  forall F : diGraph, oriented F -> inhabited (underlying F ≃ cycle_graph 4) ->
    eulerian_avoidable F.
