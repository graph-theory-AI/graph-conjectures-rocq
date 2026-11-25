(** * Independence number of K_{t+1}-minor-free graphs

Dvořák, Yepremyan, "Independence number in triangle-free graphs avoiding a minor",
arXiv:1907.12999, Conjecture 1 (1907.12999__00).

The independence number α(G) is the maximum size of a set of pairwise nonadjacent vertices of G.

Conjecture 1: for every positive integer t, if a graph G on n vertices does not contain K_{t+1} as
a minor, then α(G) >= n / t.

Encoding.  Graphs are finite and simple.  α(G) >= n / t is written n <= t α(G). *)

From GraphTheory Require Import digraph sgraph coloring minor.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Statement *)

Definition AX_kt_minor_free_independence_n_over_t : Prop :=
  forall (t n : nat) (G : sgraph),
    0 < t -> #|G| = n -> ~ minor G 'K_(t.+1) -> n <= t * α(G).
