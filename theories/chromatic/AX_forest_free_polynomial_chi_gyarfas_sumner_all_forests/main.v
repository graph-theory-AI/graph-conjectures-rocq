(** * Polynomial Gyárfás-Sumner conjecture

Chudnovsky, Scott, Seymour, Spirkl, "Polynomial bounds for chromatic number. VII. Disjoint holes",
arXiv:2202.09118, introduction (2202.09118__02).

A graph is H-free if it has no induced subgraph isomorphic to H.  A class of graphs is polynomially
χ-bounded if there is a polynomial f such that χ(G) <= f(ω(G)) for every graph G of the class.

Informal conjecture: for every forest H, the class of H-free graphs is polynomially χ-bounded.

Encoding.  The polynomial f is of the form c x^d, which is not a restriction. *)

From GraphTheory Require Import digraph sgraph coloring.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

(** [G] has an induced subgraph isomorphic to [H]. *)
Definition has_induced_copy (G H : sgraph) : Prop := inhabited (H ⇀ G).

(** [G] has no induced subgraph isomorphic to [H]. *)
Definition induced_free (G H : sgraph) : Prop := ~ has_induced_copy G H.

(** ** Definitions copied from GraphLib/chromatic.v *)

(** The class [F] is polynomially chi-bounded. *)
Definition poly_chi_bounded (F : sgraph -> Prop) : Prop :=
  exists c d : nat,
    forall G : sgraph, F G -> χ([set: G]) <= c * ω([set: G]) ^ d.

(** ** Statement *)

Definition AX_forest_free_polynomial_chi_gyarfas_sumner_all_forests : Prop :=
  forall H : sgraph,
    is_forest [set: H] -> poly_chi_bounded (fun G : sgraph => induced_free G H).
