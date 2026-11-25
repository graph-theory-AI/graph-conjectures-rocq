(** * The polynomial Gyárfás–Sumner conjecture

Scott, Seymour, Spirkl, "Polynomial bounds for chromatic number. IV. A near-polynomial bound for
excluding the five-vertex path", arXiv:2110.00278, Conjecture 1.3 (2110.00278__00).

A graph is H-free if it has no induced subgraph isomorphic to H.

Conjecture 1.3: for every forest H, there exists c > 0 such that χ(G) <= ω(G)^c for every H-free
graph G.

Encoding.  Graphs are finite and simple.  The exponent c is an integer, without loss of
generality. *)

From GraphTheory Require Import digraph sgraph coloring.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

(** [G] has an induced subgraph isomorphic to [H]. *)
Definition has_induced_copy (G H : sgraph) : Prop := inhabited (H ⇀ G).

(** ** Statement *)

Definition AX_forest_free_polynomial_chi_omega_power : Prop :=
  forall H : sgraph,
    is_forest [set: H] ->
    exists c : nat, 0 < c /\
      forall G : sgraph, ~ has_induced_copy G H -> χ([set: G]) <= ω([set: G]) ^ c.
