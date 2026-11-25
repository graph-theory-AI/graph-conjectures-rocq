(** * Hamiltonicity of Cayley graphs

Rapaport-Strasser, "Cayley color groups and Hamilton lines", Scripta Math. 24 (1959); Open Problem
Garden, hamiltonicity_of_cayley_graphs.

Let S = S^-1 be a generating set of a group Γ.  The Cayley graph of Γ and S has vertex set Γ, and
distinct vertices x and y are adjacent if x^-1 y ∈ S.

Question: is every Cayley graph Hamiltonian?  What is stated is the positive answer, for the finite
groups with at least three elements.

Encoding.  Cayley graphs are simple: the neutral element is ignored when it is in S.  They are
connected, as S generates the group.  The groups with one or two elements are excluded, because K_1
and K_2 have no Hamilton cycle. *)

From GraphTheory Require Import preliminaries digraph sgraph.
From mathcomp Require Import boot fingroup.

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

(** The (undirected) Cayley graph of the group [gT] for the connection set [S] (made symmetric,
    without the neutral element). *)
Definition cayley_graph (gT : finGroupType) (S : {set gT}) : sgraph :=
  sgraph_of_rel (fun x y : gT => (x^-1 * y)%g \in S).

(** ** Definitions copied from GraphLib/hamiltonicity.v *)

(** [c] is a Hamiltonian cycle of [G]. *)
Definition hamiltonian_cycle (G : sgraph) (c : seq G) : bool :=
  ucycleb (--) c && (size c == #|G|).
Arguments hamiltonian_cycle : clear implicits.

(** [G] is Hamiltonian. *)
Definition hamiltonian (G : sgraph) : Prop :=
  exists c : seq G, hamiltonian_cycle G c.

(** ** Definitions specific to the conjecture *)

(** [S] is closed under inverses. *)
Definition symmetric_set (gT : finGroupType) (S : {set gT}) : Prop :=
  forall x : gT, (x \in S) = (x^-1 \in S)%g.

(** ** Statement *)

Definition OPG_cayley_graphs_hamiltonian_cycle : Prop :=
  forall (gT : finGroupType) (S : {set gT}),
    2 < #|gT| -> symmetric_set S -> <<S>>%g = [set: gT] ->
    hamiltonian (cayley_graph S).
