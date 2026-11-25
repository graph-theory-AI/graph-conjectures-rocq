(** * Polynomial bounds for the Gyárfás–Sumner conjecture

Nguyen, Scott, Seymour, "A note on the Gyárfás–Sumner conjecture", arXiv:2302.08922
(2302.08922__01).

Conjecture: for every tree T there is a polynomial f such that every graph with no induced subgraph
isomorphic to T and no clique of size t has chromatic number at most f(t).

Encoding.  Graphs are finite and simple.  The chromatic number is bounded by a polynomial in the
clique number, which is equivalent.  The polynomial has the form f(t) = c t^d, without loss of
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

Definition AX_forest_free_polynomial_chi_gyarfas_sumner : Prop :=
  forall T : sgraph,
    is_tree [set: T] ->
    poly_chi_bounded (fun G : sgraph => ~ has_induced_copy G T).
