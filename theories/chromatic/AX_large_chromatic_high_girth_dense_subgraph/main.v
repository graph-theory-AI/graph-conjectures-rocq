(** * Dense subgraphs of large girth in graphs of large chromatic number

Mohar, Wu, "Triangle-free subgraphs with large fractional chromatic number", arXiv:1808.01605,
Conjecture 6 (1808.01605__01).

The girth of a graph is the minimum length of its cycles (infinite for a forest).

Conjecture 6: for all positive integers k and g >= 3, there exists a positive number c(k,g) such
that every graph with chromatic number at least c(k,g) contains a subgraph of girth at least g and
average degree at least k.

Encoding.  Graphs are finite and simple.  "H has average degree at least k" is k |V(H)| <= Σ_v d(v),
the sum of the degrees in H.  As the empty graph satisfies this inequality, H is required to be
nonempty. *)

From GraphTheory Require Import digraph sgraph coloring.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

(** The average degree of [G] is at least [a / b]. *)
Definition average_degree_ge (G : sgraph) (a b : nat) : Prop :=
  a * #|G| <= b * (\sum_(v in G) #|N(v)|).

Section Cycles.
Variables (T : eqType) (r : rel T).
Implicit Types c : seq T.

(** [c] is a cycle (without repetition, of length at least 3) of the relation [r]. *)
Definition seq_cycle c : bool := ucycleb r c && (2 < size c).

End Cycles.

(** The girth of [G] is at least [g] (true if [G] is a forest). *)
Definition girth_ge (G : sgraph) (g : nat) : Prop :=
  forall c : seq G, seq_cycle (--) c -> g <= size c.

(** ** Statement *)

Definition AX_large_chromatic_high_girth_dense_subgraph : Prop :=
  forall k g : nat, 0 < k -> 3 <= g ->
    exists c : nat, 0 < c /\
      forall G : sgraph, c <= χ([set: G]) ->
        exists H : sgraph,
          [/\ 0 < #|H|, subgraph H G, girth_ge H g & average_degree_ge H k 1].
