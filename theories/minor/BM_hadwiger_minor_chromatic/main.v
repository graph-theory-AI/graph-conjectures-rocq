(** * Hadwiger's conjecture

Hadwiger; Bondy, Murty, "Graph Theory", Appendix A, problem 41.

A graph is k-chromatic if its chromatic number is k.

Conjecture: every k-chromatic graph has a K_k minor.

Encoding.  Graphs are finite and simple. *)

From GraphTheory Require Import digraph sgraph coloring minor.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Statement *)

Definition BM_hadwiger_minor_chromatic : Prop :=
  forall (k : nat) (G : sgraph), χ([set: G]) = k -> minor G 'K_k.
