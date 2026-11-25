(** * Cores of Cayley graphs

Šámal; Open Problem Garden, cores_of_cayley_graphs.

A core is a graph all of whose endomorphisms are bijective.  The core of a finite graph G is the
core that is homomorphically equivalent to G (there are homomorphisms between them in both
directions), which is unique up to isomorphism.  For a subset S of a group, the Cayley graph of S
has the elements of the group as vertices, and distinct elements x and y are adjacent if x^-1 y
or y^-1 x is in S.

Problem: let M be an abelian group; is the core of a Cayley graph on some power of M a Cayley
graph on some power of M?

The proposition states the positive answer.

Encoding.  The group M is finite, so that the graphs are finite, and it is written
multiplicatively.  The power M^k is the group of the functions from {0,...,k-1} to M.  The exponent
0 is allowed: M^0 is the trivial group, and the core of a graph without edges is K_1.  The set S
is arbitrary; this gives the same graphs as the sets S = S^-1 without the neutral element. *)

From GraphTheory Require Import preliminaries digraph sgraph.
From mathcomp Require Import boot fingroup gproduct.

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

(** ** Definitions copied from GraphLib/homomorphism.v *)

(** There is a homomorphism from [G] to [H]. *)
Definition homs_to (G H : diGraph) : Prop := exists f : G -> H, is_dhom f.

(** [G] and [H] are homomorphically equivalent. *)
Definition hom_equiv (G H : diGraph) : Prop := homs_to G H /\ homs_to H G.

(** [G] is a core: all its endomorphisms are bijective. *)
Definition is_core (G : diGraph) : Prop := forall f : G -> G, is_dhom f -> bijective f.

(** ** Statement *)

Definition OPG_cayley_graph_core_is_cayley : Prop :=
  forall M : finGroupType, abelian [set: M] ->
  forall (k : nat) (S : {set {dffun forall i : 'I_k, M}}),
    exists (m : nat) (S' : {set {dffun forall i : 'I_m, M}}),
      is_core (cayley_graph S') /\ hom_equiv (cayley_graph S) (cayley_graph S').
