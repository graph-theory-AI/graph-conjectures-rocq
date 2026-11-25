(** * Birmelé's conjecture on long cycles

Birmelé; Bondy, Murty, "Graph Theory", Appendix A, problem 66.

Two cycles intersect if they have a common vertex.  A set of vertices meets a cycle if it contains
a vertex of this cycle.

Conjecture: if any two cycles of length at least k in a graph intersect, then the graph has a set
of k vertices meeting every cycle of length at least k.

Encoding.  Cycles are sequences of vertices, so that their length is the size of the sequence.
The set has at most k vertices, as a graph may have fewer than k vertices.
The condition k >= 3 is added.  It is implicit in the source, as the proposition is false for
k <= 2: in the complete graph K_5, any two cycles intersect, and no set of two vertices meets all
cycles. *)

From GraphTheory Require Import digraph sgraph.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

Section Cycles.
Variables (T : eqType) (r : rel T).
Implicit Types c : seq T.

(** [c] is a cycle (without repetition, of length at least 3) of the relation [r]. *)
Definition seq_cycle c : bool := ucycleb r c && (2 < size c).

End Cycles.

(** ** Statement *)

Definition BM_birmele_long_cycles_pairwise_intersecting_hitting_set : Prop :=
  forall (k : nat) (G : sgraph),
    3 <= k ->
    (forall c d : seq G,
       seq_cycle (--) c -> k <= size c -> seq_cycle (--) d -> k <= size d ->
       exists x : G, (x \in c) && (x \in d)) ->
    exists S : {set G},
      #|S| <= k /\
      forall c : seq G, seq_cycle (--) c -> k <= size c -> exists x : G, (x \in S) && (x \in c).
