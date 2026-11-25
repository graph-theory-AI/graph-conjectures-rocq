(** * Polynomial bounds on χ in terms of τ_d

Scott, Seymour, "Polynomial bounds for chromatic number. V. Excluding a tree of radius two and a
complete multipartite graph", arXiv:2202.05557, question of the introduction (2202.05557__02).

A class of graphs is hereditary if it is closed under taking induced subgraphs.  For d >= 1, τ_d(G)
is the maximum t such that G contains, as a subgraph that need not be induced, the complete
d-partite graph with parts of size t.

Question: let C be a hereditary class of graphs and d >= 1.  Suppose that, for some function f,
χ(G) <= f(τ_d(G)) for every G in C.  Can we always choose f to be a polynomial?  What if d = 2?

The proposition states the positive answer, for all d >= 1.

Encoding.  Graphs are finite and simple, and classes are closed under isomorphism.  "τ_d(G) = t" is
a relation between G, d and t (for d >= 1, exactly one t satisfies it).  The values of f
and the coefficients of the polynomial are natural numbers, without loss of generality (they can be
increased).  The polynomial is given by the list of its coefficients, the constant one first. *)

From GraphTheory Require Import bij digraph sgraph coloring.
From mathcomp Require Import boot algebra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

(** A class of graphs is closed under isomorphism. *)
Definition iso_closed (C : sgraph -> Prop) : Prop :=
  forall G H : sgraph, C G -> diso G H -> C H.

(** A class of graphs is closed under taking induced subgraphs on subsets of vertices. *)
Definition induced_closed (C : sgraph -> Prop) : Prop :=
  forall (G : sgraph) (S : {set G}), C G -> C (induced S).

(** A class of graphs is hereditary. *)
Definition hereditary_class (C : sgraph -> Prop) : Prop :=
  iso_closed C /\ induced_closed C.

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

Definition AX_hereditary_tau_d_bounded_implies_polynomial_esperet : Prop :=
  forall (C : sgraph -> Prop) (d : nat), hereditary_class C -> 1 <= d ->
    (exists f : nat -> nat, forall (G : sgraph) (t : nat),
       C G -> multipartite_number G d t -> χ([set: G]) <= f t) ->
    exists p : seq nat, forall (G : sgraph) (t : nat),
      C G -> multipartite_number G d t -> χ([set: G]) <= horner_rec p t.
