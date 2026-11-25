(** * The Erdős-Hajnal property for C_8 and its complement

Chudnovsky, Scott, Seymour, Spirkl, "Erdős-Hajnal for graphs with no 5-hole", arXiv:2102.04994
(2102.04994__00).

A set X of graphs has the Erdős-Hajnal property if there exists τ > 0 such that every graph G
without induced subgraph isomorphic to a member of X has a clique or a stable set of size at least
|G|^τ, where |G| is the number of vertices of G.

Question: does the set of C_8 and its complement have the Erdős-Hajnal property?

The proposition states that the answer is yes.

Encoding.  Graphs are finite and simple.  The constant is τ = 1/c for a positive integer c, which is
not a restriction, and the inequality |S| >= |G|^τ is written |G| <= |S|^c. *)

From GraphTheory Require Import preliminaries digraph sgraph dom.
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

(** [G] has an induced subgraph isomorphic to [H]. *)
Definition has_induced_copy (G H : sgraph) : Prop := inhabited (H ⇀ G).

(** [G] has no induced subgraph isomorphic to [H]. *)
Definition induced_free (G H : sgraph) : Prop := ~ has_induced_copy G H.

(** The cycle on [n] vertices ([3 <= n] is meant). *)
Definition cycle_graph (n : nat) : sgraph :=
  sgraph_of_rel (fun i j : 'I_n => (val i).+1 %% n == val j).

(** ** Definitions copied from GraphLib/extremal.v *)

(** [S] is homogeneous: a clique or a stable set. *)
Definition homogeneous_set (G : sgraph) (S : {set G}) : Prop :=
  clique S \/ stable S.

(** ** Statement *)

Definition AX_erdos_hajnal_c8_complement_c8 : Prop :=
  exists c : nat, 0 < c /\
    forall G : sgraph,
      induced_free G (cycle_graph 8) -> induced_free G (compl (cycle_graph 8)) ->
      exists S : {set G}, homogeneous_set S /\ #|G| <= #|S| ^ c.
