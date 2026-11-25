(** * Disjoint union of two good trees

Chudnovsky, Scott, Seymour, Spirkl, "Polynomial bounds for chromatic number VII. Disjoint holes",
arXiv:2202.09118 (2202.09118__03).

A graph is H-free if it has no induced subgraph isomorphic to H.  A class of graphs is polynomially
χ-bounded if there is a polynomial f such that χ(G) <= f(ω(G)) for every graph G of the class.  A
forest H is good if the class of H-free graphs is polynomially χ-bounded.

Problem: it is not known that if trees H_1, H_2 are good, then the disjoint union of H_1 and H_2 is
also good.

The proposition states that the disjoint union of two good trees is good.

Encoding.  Graphs are finite and simple.  The polynomial has the form f(t) = c t^d, without loss of
generality. *)

From GraphTheory Require Import digraph sgraph coloring.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

(** [G] has an induced subgraph isomorphic to [H]. *)
Definition has_induced_copy (G H : sgraph) : Prop := inhabited (H ⇀ G).

(** ** Definitions copied from GraphLib/chromatic.v *)

(** The class [F] is polynomially chi-bounded. *)
Definition poly_chi_bounded (F : sgraph -> Prop) : Prop :=
  exists c d : nat,
    forall G : sgraph, F G -> χ([set: G]) <= c * ω([set: G]) ^ d.

(** ** Definitions specific to the conjecture *)

(** [H] is good: the class of [H]-free graphs is polynomially chi-bounded. *)
Definition good (H : sgraph) : Prop :=
  poly_chi_bounded (fun G : sgraph => ~ has_induced_copy G H).

(** ** Statement *)

(** [sjoin H1 H2] is the disjoint union of [H1] and [H2]. *)
Definition AX_poly_chi_bounded_trees_disjoint_union : Prop :=
  forall H1 H2 : sgraph,
    is_tree [set: H1] -> is_tree [set: H2] ->
    good H1 -> good H2 -> good (sjoin H1 H2).
