(** * Constricting sets of hole lengths of density zero

Scott, Seymour, "Induced subgraphs of graphs with large chromatic number. IV. Consecutive holes",
J. Combin. Theory B 132 (2018), arXiv:1509.06563, Problem 1.6 (1509.06563__02).

A hole is an induced cycle of length at least 4.  A set F of integers is k-constricting if there
exists n such that every graph with chromatic number at least n contains either a clique with k
vertices or a hole with length in F.  It is constricting if it is k-constricting for every k.

Problem 1.6: is there an infinite set F of positive integers such that F is constricting and has
density 0?

The proposition states the positive answer, conjectured by the authors.

Encoding.  Graphs are finite and simple.  F is a boolean predicate on the natural numbers.  It has
density 0 if for every positive rational number ε, |F ∩ {1,...,n}| <= ε n for n large enough. *)

From GraphTheory Require Import digraph sgraph coloring.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

Section Sequences.
Variable T : finType.
Implicit Types c : seq T.

(** The list of the pairs of consecutive elements of the cyclic sequence [c]: the edges of a
    closed walk. *)
Definition seq_cycle_edge_list c : seq {set T} :=
  map (fun p : T * T => [set p.1; p.2]) (zip c (rot 1 c)).

End Sequences.

Section Cycles.
Variables (T : eqType) (r : rel T).
Implicit Types c : seq T.

(** [c] is a cycle (without repetition, of length at least 3) of the relation [r]. *)
Definition seq_cycle c : bool := ucycleb r c && (2 < size c).

End Cycles.

Section InducedPathsCycles.
Variable G : sgraph.
Implicit Types (c : seq G) (u v : G).

(** Adjacent vertices of [c] are consecutive in the cyclic sequence [c]. *)
Definition cyclic_chordless c : Prop :=
  forall u v, u \in c -> v \in c -> u -- v -> [set u; v] \in seq_cycle_edge_list c.

(** [c] is an induced cycle (of length at least 3). *)
Definition chordless_cycle c : Prop := seq_cycle (--) c /\ cyclic_chordless c.

(** [c] is a hole: an induced cycle of length at least 4. *)
Definition hole c : Prop := chordless_cycle c /\ 3 < size c.

(** [G] has a hole of length [L]. *)
Definition has_hole_of_length (L : nat) : Prop := exists c, hole c /\ size c = L.

End InducedPathsCycles.
Arguments cyclic_chordless {G} c.
Arguments hole {G} c.

(** ** Definitions copied from GraphLib/chromatic.v *)

(** The set [F] of integers is [k]-constricting: the graphs of large chromatic number and of
    clique number less than [k] have a hole whose length is in [F]. *)
Definition k_constricting (F : nat -> Prop) (k : nat) : Prop :=
  exists n : nat, forall G : sgraph,
    n <= χ([set: G]) ->
    k <= ω([set: G]) \/ exists L : nat, F L /\ has_hole_of_length G L.

(** [F] is constricting. *)
Definition constricting (F : nat -> Prop) : Prop := forall k : nat, k_constricting F k.

(** ** Definitions specific to the conjecture *)

(** The number of elements of [F] in [{1, ..., n}]. *)
Definition count_up_to (F : pred nat) (n : nat) : nat := #|[set i : 'I_n | F (val i).+1]|.

(** [F] has density 0 ([p / q] is the [ε] of the opening comment). *)
Definition density_zero (F : pred nat) : Prop :=
  forall p q : nat, 0 < p -> 0 < q ->
    exists N : nat, forall n : nat, N <= n -> q * count_up_to F n <= p * n.

(** ** Statement *)

Definition AX_constricting_hole_lengths_density_zero : Prop :=
  exists F : pred nat,
    [/\ forall n : nat, F n -> 0 < n,
        forall n : nat, exists m : nat, n <= m /\ F m,
        constricting F
      & density_zero F].
