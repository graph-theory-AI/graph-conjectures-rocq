(** * Cycles plus copies of K_4

"Open problems of the 33rd Workshop on Cycles and Colourings", arXiv:2511.02892, Problem 3.1,
presented by Haxell (2511.02892__02).

Problem 3.1: let G be a disjoint union of cycles, and let H be a disjoint union of K_4's on the same
vertex set.  Is G ∪ H 4-colourable?

The proposition states the positive answer.

Encoding.  Graphs are finite and simple.  The components of H are the classes of a map p from the
vertices to 'I_n.  Isolated vertices are allowed in G, which is equivalent: they can be put on
new cycles, whose new vertices are covered by new K_4's. *)

From GraphTheory Require Import preliminaries digraph sgraph coloring.
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

(** ** Definitions specific to the conjecture *)

(** [G] is a disjoint union of cycles and isolated vertices: every degree is 0 or 2. *)
Definition cycle_union (G : sgraph) : Prop :=
  forall v : G, #|N(v)| = 0 \/ #|N(v)| = 2.

(** Each class of [p] has four vertices. *)
Definition k4_parts (G : sgraph) (n : nat) (p : G -> 'I_n) : Prop :=
  forall i : 'I_n, #|[set v | p v == i]| = 4.

(** The graph [G ∪ H], where [H] consists of cliques on the classes of [p]. *)
Definition union_k4 (G : sgraph) (n : nat) (p : G -> 'I_n) : sgraph :=
  sgraph_of_rel (fun x y : G => (x -- y) || (p x == p y)).

(** ** Statement *)

Definition AX_cycles_union_k4_copies_4_colorable : Prop :=
  forall (G : sgraph) (n : nat) (p : G -> 'I_n),
    cycle_union G -> k4_parts p -> χ([set: union_k4 p]) <= 4.
