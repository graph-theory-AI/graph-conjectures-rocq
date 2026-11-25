(** * Kempe equivalence in graphs with no K_t minor

Bonamy, Heinrich, Legrand-Duchesne, Narboni, "On a recolouring version of Hadwiger's conjecture",
arXiv:2103.10684, Question 1.7 (2103.10684__01).

Given a proper k-colouring and two colours, a Kempe chain is a component of the subgraph induced by
the vertices that have these colours; a Kempe change exchanges the two colours on a Kempe chain.
Two colourings are Kempe equivalent if one is obtained from the other by a sequence of Kempe
changes.

Question 1.7: is there a constant c such that, for every t, all the proper (c t)-colourings of a
graph with no K_t minor are Kempe equivalent?  The positive answer is stated.

Encoding.  The constant c is a positive integer.  For a real c and a number of colours rounded up or
down, the question is equivalent (the constant may change). *)

From GraphTheory Require Import digraph sgraph coloring minor.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/chromatic.v *)

(** [col] is a proper colouring of [G]. *)
Definition proper_coloring (G : sgraph) (C : finType) (col : G -> C) : bool :=
  coloring (preim_partition col [set: G]) [set: G].

(** [S] is a Kempe chain of [col] for the colours [a] and [b]: a component of the subgraph
    induced by these colours. *)
Definition kempe_chain (G : sgraph) (k : nat) (col : G -> 'I_k) (a b : 'I_k)
    (S : {set G}) : Prop :=
  S \in components [set v | (col v == a) || (col v == b)].

(** [col'] is obtained from [col] by exchanging the two colours of a Kempe chain. *)
Definition kempe_change (G : sgraph) (k : nat) (col col' : G -> 'I_k) : Prop :=
  exists (a b : 'I_k) (S : {set G}),
    [/\ a != b, kempe_chain col a b S &
        forall v : G, col' v = if v \in S then (if col v == a then b else a) else col v].

(** [col'] is obtained from [col] by at most [n] Kempe changes. *)
Fixpoint kempe_reach_le (G : sgraph) (k n : nat) (col col' : G -> 'I_k) {struct n} : Prop :=
  match n with
  | 0 => col =1 col'
  | n'.+1 =>
      col =1 col' \/ exists c : G -> 'I_k, kempe_change col c /\ kempe_reach_le n' c col'
  end.

(** ** Statement *)

Definition AX_kt_minor_free_recoloring_single_class : Prop :=
  exists c : nat, 0 < c /\
    forall (t : nat) (G : sgraph) (col1 col2 : G -> 'I_(c * t)),
      ~ minor G 'K_t -> proper_coloring col1 -> proper_coloring col2 ->
      exists n : nat, kempe_reach_le n col1 col2.
