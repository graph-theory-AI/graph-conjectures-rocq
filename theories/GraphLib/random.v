(** * Finite probability and random graphs

    Probabilities are given by weights on finite types, and [G(n,p)] by its edge sets. *)

From GraphTheory Require Import preliminaries digraph sgraph.
From mathcomp Require Import boot order algebra.
From GC.GraphLib Require Import misc.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** [P n] holds with high probability: its probability tends to 1.  The probabilities of the
    elements of the finite type [T n] are the integers [w n x], divided by their sum. *)
Definition whp
    (T : nat -> finType) (w : forall n : nat, T n -> nat)
    (P : forall n : nat, pred (T n)) : Prop :=
  forall a b : nat, 0 < a -> a <= b ->
    eventually (fun n =>
      0 < \sum_x w n x /\
      b * (\sum_(x | P n x) w n x) >= (b - a) * (\sum_x w n x)).

(** The probability that the edge set of the random graph [G(n,p)] on [0, ..., n-1] satisfies
    [P]. *)
Definition gnp_probability (R : realFieldType) (p : R) (n : nat) (P : pred {set {set 'I_n}}) : R :=
  (\sum_(E : {set {set 'I_n}} | (E \subset E('K_n)) && P E)
    p ^+ #|E| * (1 - p) ^+ (#|E('K_n)| - #|E|))%R.

(** The edge set of the random graph [G(n,p)] satisfies [P n] with high probability. *)
Definition gnp_whp (R : realFieldType) (p : R) (P : forall n : nat, pred {set {set 'I_n}}) : Prop :=
  forall eps : R, (0 < eps)%R -> eventually (fun n => (1 - eps <= gnp_probability p (P n))%R).
