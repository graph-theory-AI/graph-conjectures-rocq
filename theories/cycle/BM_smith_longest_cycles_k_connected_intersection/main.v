(** * Smith's conjecture on longest cycles

S. Smith, see Grötschel (1984); Bondy, Murty, "Graph Theory", Appendix A, problem 64.

A longest cycle of a graph is a cycle of maximum length.

Conjecture: in a k-connected graph, k >= 2, any two longest cycles have at least k vertices in
common.

Encoding.  Graphs are simple.  A k-connected graph has more than k vertices.  Cycles are sequences
of vertices.  The two longest cycles may be the same, which is harmless as a k-connected graph,
k >= 2, has a cycle of length greater than k. *)

From GraphTheory Require Import digraph sgraph connectivity.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

Section Cycles.
Variables (T : eqType) (r : rel T).
Implicit Types c d : seq T.

(** [c] is a cycle (without repetition, of length at least 3) of the relation [r]. *)
Definition seq_cycle c : bool := ucycleb r c && (2 < size c).

(** [c] is a longest cycle of [r]. *)
Definition seq_longest_cycle c : Prop :=
  seq_cycle c /\ forall d, seq_cycle d -> size d <= size c.

End Cycles.

(** ** Statement *)

Definition BM_smith_longest_cycles_k_connected_intersection : Prop :=
  forall (k : nat) (G : sgraph) (c d : seq G),
    2 <= k -> k.-connected G ->
    seq_longest_cycle (--) c -> seq_longest_cycle (--) d ->
    k <= #|[set:: c] :&: [set:: d]|.
