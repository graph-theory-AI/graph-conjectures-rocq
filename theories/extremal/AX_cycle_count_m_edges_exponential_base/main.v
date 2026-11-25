(** * Maximum number of cycles of a graph with m edges

Dvořák, Morrison, Noel, Norin, Postle, "Bounding the number of cycles in a graph in terms of its
degree sequence", arXiv:1907.12091, Conjecture 2 (1907.12091__00).

Conjecture: every simple graph with m edges has at most O(κ^m) cycles, where κ = (2 + 2√2)^(1/5).

Encoding.  The cycles are the subgraphs that are cycles: [cycle_count] counts each of them once.
The inequality is raised to the power 5.  It is written in an arbitrary real closed field, which is
equivalent to real numbers as √2 is algebraic.  The constant of O(κ^m) is a natural number, and the
bound holds for all m: this is equivalent, as κ > 1. *)

From GraphTheory Require Import digraph sgraph.
From mathcomp Require Import boot order algebra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.Theory GRing.Theory Num.Theory.

(** ** Definitions copied from GraphLib/extremal.v *)

(** The number of cycles of length [L] of [G] ([3 <= L] is meant). *)
Definition cycle_count_length (G : sgraph) (L : nat) : nat :=
  #|[set t : L.-tuple G | ucycleb (--) (val t)]| %/ (2 * L).

(** The number of cycles of [G]. *)
Definition cycle_count (G : sgraph) : nat := \sum_(3 <= L < #|G|.+1) cycle_count_length G L.

(** ** Statement *)

Definition AX_cycle_count_m_edges_exponential_base : Prop :=
  exists C : nat, forall (R : rcfType) (G : sgraph),
    ((cycle_count G)%:R ^+ 5 <= C%:R * (2 + 2 * Num.sqrt 2) ^+ #|E(G)| :> R)%R.
