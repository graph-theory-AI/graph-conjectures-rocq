(** * Every forest is good

Chudnovsky, Scott, Seymour, Spirkl, "Polynomial bounds for chromatic number VI. Adding a four-vertex
path", arXiv:2202.10412 (2202.10412__00).

A graph is H-free if it has no induced subgraph isomorphic to H.  A class of graphs is polynomially
χ-bounded if there is a polynomial f such that χ(G) <= f(ω(G)) for every graph G of the class.  A
graph H is good if the class of H-free graphs is polynomially χ-bounded.

Conjecture: every forest is good.

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

Definition AX_forest_free_polynomial_chi_good : Prop :=
  forall H : sgraph,
    is_forest [set: H] ->
    poly_chi_bounded (fun G : sgraph => ~ has_induced_copy G H).
