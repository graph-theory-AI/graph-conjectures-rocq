(** * Every forest is multibounding

Nguyen, Scott, Seymour, "Polynomial bounds for chromatic number VIII. Excluding a path and a
complete multipartite graph", arXiv:2303.11766, Conjecture 1.6 (2303.11766__00).

A graph is H-free if it has no induced subgraph isomorphic to H.  K_d(t) is the complete d-partite
graph with parts of size t.  A graph H is multibounding if, for every d >= 1, there is a polynomial
f such that, for all t >= 1, every H-free graph G with no subgraph isomorphic to K_d(t) satisfies
χ(G) <= f(t).

Conjecture: every forest is multibounding.

Encoding.  Graphs are finite and simple.  The polynomial has the form f(t) = c t^e, without loss of
generality.  The numbers c and e are given by functions of d, which is equivalent by countable
choice. *)

From GraphTheory Require Import digraph sgraph coloring.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

(** [G] has an induced subgraph isomorphic to [H]. *)
Definition has_induced_copy (G H : sgraph) : Prop := inhabited (H ⇀ G).

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

(** ** Definitions specific to the conjecture *)

(** [H] is multibounding. *)
Definition multibounding (H : sgraph) : Prop :=
  exists c e : nat -> nat,
    forall d : nat, 1 <= d ->
      forall (t : nat) (G : sgraph),
        1 <= t ->
        ~ has_induced_copy G H ->
        ~ subgraph (complete_multipartite d t) G ->
        χ([set: G]) <= c d * t ^ e d.

(** ** Statement *)

Definition AX_forest_free_multibounding_chi_bound : Prop :=
  forall H : sgraph,
    is_forest [set: H] ->
    multibounding H.
