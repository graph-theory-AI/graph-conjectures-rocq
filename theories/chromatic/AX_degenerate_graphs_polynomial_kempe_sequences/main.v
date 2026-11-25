(** * Kempe changes in degenerate graphs

Bonamy, Delecroix, Legrand-Duchesne, "Kempe changes in degenerate graphs", arXiv:2112.02313
(2112.02313__00).

Given a proper k-colouring and two colours, a Kempe chain is a component of the subgraph induced by
the vertices that have these colours; a Kempe change exchanges the two colours on a Kempe chain.
A graph is d-degenerate if each of its nonempty subgraphs has a vertex of degree at most d.

Question: can any two proper k-colourings of a (k-1)-degenerate graph on n vertices be connected by
a sequence of Kempe changes whose length is polynomial in n?  The positive answer is stated.

Encoding.  The polynomial may depend on k, and is of the form c n^d, which is not a restriction.
For k = 0 (truncated subtraction) the statement is trivial. *)

From GraphTheory Require Import digraph sgraph coloring.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

(** The subgraph induced by [W] is [k]-degenerate: each nonempty subset [S] of [W] has a
    vertex with at most [k] neighbours in [S]. *)
Definition degenerate_on (G : sgraph) (W : {set G}) (k : nat) : Prop :=
  forall S : {set G}, S \subset W -> S != set0 -> exists x, (x \in S) /\ #|N(x) :&: S| <= k.
Arguments degenerate_on {G} W k.

(** [G] is [k]-degenerate. *)
Definition degenerate (G : sgraph) (k : nat) : Prop :=
  degenerate_on [set: G] k.

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

Definition AX_degenerate_graphs_polynomial_kempe_sequences : Prop :=
  forall k : nat, exists c d : nat, forall (G : sgraph) (col1 col2 : G -> 'I_k),
    degenerate G (k - 1) -> proper_coloring col1 -> proper_coloring col2 ->
    kempe_reach_le (c * #|G| ^ d) col1 col2.
