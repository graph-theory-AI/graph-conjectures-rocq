(** * Polynomial χ-boundedness of H-free graphs for a forest H

Scott, Seymour, "Polynomial bounds for chromatic number. V. Excluding a tree of radius two and a
complete multipartite graph", arXiv:2202.05557, Conjecture 1.3 (2202.05557__00).

A graph G is H-free if no induced subgraph of G is isomorphic to H.

Conjecture 1.3: for every forest H, there is a polynomial f such that χ(G) <= f(ω(G)) for every
H-free graph G.

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

(** ** Statement *)

Definition AX_forest_free_polynomial_chi_bounded : Prop :=
  forall H : sgraph,
    is_forest [set: H] ->
    poly_chi_bounded (fun G : sgraph => ~ has_induced_copy G H).
