(** * A hereditary class that is χ-bounded but not polynomially χ-bounded

Bonamy, Pilipczuk, "Graphs of bounded cliquewidth are polynomially χ-bounded", arXiv:1910.00697
(1910.00697__00); the problem is from Esperet's habilitation thesis.

A class of graphs is hereditary if it is closed under taking induced subgraphs.  It is χ-bounded if
there is a function f such that χ(G) <= f(ω(G)) for every graph G of the class, and polynomially
χ-bounded if f can be chosen to be a polynomial.

Question: is there a hereditary class of graphs that is χ-bounded but not polynomially χ-bounded?

The proposition states the positive answer.

Encoding.  Graphs are finite and simple.  A hereditary class is moreover closed under isomorphism.
The polynomial has the form f(t) = c t^d, without loss of generality. *)

From GraphTheory Require Import digraph sgraph coloring.
From mathcomp Require Import boot.

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

(** ** Definitions copied from GraphLib/chromatic.v *)

(** The class [F] is chi-bounded: on its graphs, the chromatic number is bounded by a function
    of the clique number. *)
Definition chi_bounded (F : sgraph -> Prop) : Prop :=
  exists f : nat -> nat,
    forall G : sgraph, F G -> χ([set: G]) <= f (ω([set: G])).

(** The class [F] is polynomially chi-bounded. *)
Definition poly_chi_bounded (F : sgraph -> Prop) : Prop :=
  exists c d : nat,
    forall G : sgraph, F G -> χ([set: G]) <= c * ω([set: G]) ^ d.

(** ** Statement *)

Definition AX_chi_bounded_not_polynomially_chi_bounded : Prop :=
  exists F : sgraph -> Prop,
    [/\ hereditary_class F, chi_bounded F & ~ poly_chi_bounded F].
