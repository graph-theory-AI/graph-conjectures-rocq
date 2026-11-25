(** * Self-isolating graphs

Chudnovsky, Scott, Seymour, Spirkl, "Polynomial bounds for chromatic number VII. Disjoint holes",
arXiv:2202.09118 (2202.09118__04).

A graph is H-free if it has no induced subgraph isomorphic to H.  A graph H is self-isolating if,
for every non-decreasing polynomial ψ : N -> N, there is a polynomial φ such that every graph G with
χ(G) > φ(ω(G)) has a set A of vertices with χ(G[A]) > ψ(ω(G[A])) such that either G[A] is H-free, or
G contains an induced copy of H whose vertex set is disjoint from A and has no edge to A.

Question: are all graphs self-isolating?

The proposition states the positive answer.

Encoding.  Graphs are finite and simple.  The polynomials ψ and φ are monomials c x^d and c' x^d',
which is equivalent: every polynomial is bounded by a monomial on the positive integers, and only
these matter since G and A are nonempty when the inequalities hold. *)

From GraphTheory Require Import digraph sgraph coloring.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

(** [A] and [B] are disjoint and there is no edge between them. *)
Definition anticomplete (G : sgraph) (A B : {set G}) : bool :=
  [disjoint A & B] && ~~ neighbor A B.

(** [G] has an induced subgraph isomorphic to [H]. *)
Definition has_induced_copy (G H : sgraph) : Prop := inhabited (H ⇀ G).

(** [G] has no induced subgraph isomorphic to [H]. *)
Definition induced_free (G H : sgraph) : Prop := ~ has_induced_copy G H.

(** ** Definitions specific to the conjecture *)

(** [H] is self-isolating. *)
Definition self_isolating (H : sgraph) : Prop :=
  forall c d : nat, exists c' d' : nat,
    forall G : sgraph, c' * ω([set: G]) ^ d' < χ([set: G]) ->
      exists A : {set G}, c * ω(A) ^ d < χ(A) /\
        (induced_free (induced A) H \/
         exists S : {set G}, inhabited (induced S ≃ H) /\ anticomplete S A).

(** ** Statement *)

Definition AX_poly_chi_bounded_self_isolating_all : Prop :=
  forall H : sgraph, self_isolating H.
