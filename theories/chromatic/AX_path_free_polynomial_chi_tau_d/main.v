(** * Excluding a path and a complete multipartite graph

Scott, Seymour, "Polynomial bounds for chromatic number. V. Excluding a tree of radius two and a
complete multipartite graph", arXiv:2202.05557, question after Theorem 1.6 (2202.05557__01).

A graph is H-free if it has no induced subgraph isomorphic to H.  For d >= 1, τ_d(G) is the maximum
t such that G has a subgraph, not necessarily induced, isomorphic to the complete d-partite graph
with d parts of size t.

Question: is it true that, if H is a path, then for every d >= 1 there is a polynomial f such that
χ(G) <= f(τ_d(G)) for every H-free graph G?  The positive answer is stated.

Encoding.  "τ_d(G) = t" is a relation between G and t.  The polynomial f has coefficients in nat,
which is not a restriction for an upper bound on nat: it is the list [p] of its coefficients, and
[horner_rec p t] is its value at t. *)

From GraphTheory Require Import preliminaries digraph sgraph coloring.
From mathcomp Require Import boot algebra.

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

(** The path on [n] vertices. *)
Definition path_graph (n : nat) : sgraph := sgraph_of_rel (fun i j : 'I_n => (val i).+1 == val j).

Section CompleteMultipartite.
Variables k m : nat.

(** Vertices in different parts. *)
Definition complete_multipartite_rel : rel ('I_k * 'I_m) := fun x y => x.1 != y.1.

Lemma complete_multipartite_sym : symmetric complete_multipartite_rel.
Proof. by move=> x y; rewrite /complete_multipartite_rel eq_sym. Qed.

Lemma complete_multipartite_irrefl : irreflexive complete_multipartite_rel.
Proof. by move=> x; rewrite /complete_multipartite_rel eqxx. Qed.

(** The complete multipartite graph with [k] parts of size [m]. *)
Definition complete_multipartite : sgraph :=
  SGraph complete_multipartite_sym complete_multipartite_irrefl.

End CompleteMultipartite.

(** ** Definitions copied from GraphLib/extremal.v *)

(** The largest [t] such that [G] has a subgraph isomorphic to the complete [d]-partite graph with
    parts of size [t] is [t]. *)
Definition multipartite_number (G : sgraph) (d t : nat) : Prop :=
  subgraph (complete_multipartite d t) G /\
  forall s : nat, subgraph (complete_multipartite d s) G -> s <= t.

(** ** Statement *)

Definition AX_path_free_polynomial_chi_tau_d : Prop :=
  forall k d : nat, 1 <= d ->
    exists p : seq nat, forall (G : sgraph) (t : nat),
      induced_free G (path_graph k) -> multipartite_number G d t -> χ([set: G]) <= horner_rec p t.
