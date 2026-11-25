(** * Cycles of length 0 mod k in graphs of large chromatic number

Brewster, McGuinness, Moore, Noel, "A dichotomy theorem for circular colouring reconfiguration",
arXiv:1508.05573; Open Problem Garden, cycles_in_graphs_of_large_chromatic_number.

Conjecture: if χ(G) > k, then G contains at least (k+1)(k-1)!/2 cycles of length 0 mod k.

Encoding.  Graphs are finite and simple.  The condition k >= 3 is added: the bound does not hold
for k = 1 (take K_2) nor for k = 2 (take a 5-cycle).  The inequality is multiplied by 2.  The
number of cycles of length L >= 3 is the number of sequences of L distinct vertices, where
consecutive vertices are adjacent as well as the last and the first one, divided by 2L: each cycle
corresponds to 2L sequences. *)

From GraphTheory Require Import digraph sgraph coloring.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/extremal.v *)

(** The number of cycles of length [L] of [G] ([3 <= L] is meant). *)
Definition cycle_count_length (G : sgraph) (L : nat) : nat :=
  #|[set t : L.-tuple G | ucycleb (--) (val t)]| %/ (2 * L).

(** ** Definitions specific to the conjecture *)

(** The number of cycles of [G] whose length is a multiple of [k]. *)
Definition count_cycles_mod (G : sgraph) (k : nat) : nat :=
  \sum_(L < #|G|.+1 | (2 < L) && (k %| L)) cycle_count_length G L.

(** ** Statement *)

Definition OPG_high_chromatic_cycles_0_mod_k : Prop :=
  forall (k : nat) (G : sgraph),
    2 < k -> k < χ([set: G]) ->
    k.+1 * (k.-1)`! <= 2 * count_cycles_mod G k.
