(** * Dimension of posets with planar cover graphs

Joret, Micek, Wiechert, "Planar posets have dimension at most linear in their height", SIAM J.
Discrete Math. 31 (2017), arXiv:1612.07540, open problem (1612.07540__00).

The posets are finite.  The dimension of a poset is the minimum number of linear orders whose
intersection is the order of the poset.  Its height is the maximum size of a chain.  Its cover
graph is the undirected graph whose edges are the pairs ab such that a < b and there is no c
with a < c < b.

Problem: is the dimension of the posets with planar cover graphs bounded by a linear function of
their height (or any polynomial function)?

The proposition states the positive answer for a linear function: there is a constant C such that
the dimension of every poset of height at most h with a planar cover graph is at most C h.

Encoding.  A graph is planar if it has no minor K_5 or K_{3,3} (Wagner's theorem).  An additive
constant would change nothing but C, as h >= 1 if the poset is not empty.  A poset with at most one
element has dimension 0. *)

From GraphTheory Require Import preliminaries digraph sgraph minor.
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

(** [le] is an order. *)
Definition is_order (X : finType) (le : rel X) : Prop :=
  [/\ reflexive le, antisymmetric le & transitive le].

(** [l] is a linear order. *)
Definition is_linear_order (X : finType) (l : rel X) : Prop :=
  [/\ reflexive l, antisymmetric l, transitive l & total l].

(** The list [ls] is a realizer of [le]: linear extensions whose intersection is [le]. *)
Definition realizer (X : finType) (le : rel X) (ls : seq (rel X)) : Prop :=
  (forall i : nat, i < size ls ->
     is_linear_order (nth (fun _ _ => false) ls i) /\
     subrel le (nth (fun _ _ => false) ls i)) /\
  (forall x y : X, le x y <->
     (forall i : nat, i < size ls -> (nth (fun _ _ => false) ls i) x y)).

(** The (Dushnik-Miller) dimension of the order [le] is at most [d]. *)
Definition poset_dim_le (X : finType) (le : rel X) (d : nat) : Prop :=
  exists ls : seq (rel X), size ls <= d /\ realizer le ls.

(** The height (maximum size of a chain) is at most [h]. *)
Definition poset_height_le (X : finType) (le : rel X) (h : nat) : Prop :=
  forall A : {set X}, {in A &, total le} -> #|A| <= h.

(** [y] covers [x]. *)
Definition poset_cover_rel (X : finType) (le : rel X) (x y : X) : bool :=
  [&& le x y, x != y &
      [forall z : X, (le x z && le z y) ==> ((z == x) || (z == y))]].

(** The cover graph (undirected Hasse diagram) of the order [le]. *)
Definition poset_cover_graph (X : finType) (le : rel X) : sgraph :=
  sgraph_of_rel (poset_cover_rel le).

(** ** Definitions copied from GraphLib/topological.v *)

(** [G] is planar: it has no minor [K_5] or [K_3,3]. *)
Definition planar (G : sgraph) : Prop :=
  ~ minor G 'K_5 /\ ~ minor G (KB 3 3).

(** ** Statement *)

Definition AX_planar_cover_graph_poset_dimension_height : Prop :=
  exists C : nat,
    forall (X : finType) (le : rel X) (h : nat),
      is_order le ->
      planar (poset_cover_graph le) ->
      poset_height_le le h ->
      poset_dim_le le (C * h).
