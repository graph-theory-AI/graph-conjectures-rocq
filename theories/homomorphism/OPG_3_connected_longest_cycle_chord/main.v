(** * Chords of longest cycles

Thomassen; Open Problem Garden, chords_of_longest_cycles.

A chord of a cycle C is an edge that is not in E(C) and has both ends in V(C).  A longest cycle of
a graph is a cycle of maximum length.

Conjecture: if G is a 3-connected graph, every longest cycle in G has a chord.

Encoding.  Graphs are finite and simple.  A 3-connected graph has more than three vertices.  Cycles
are sequences of vertices. *)

From GraphTheory Require Import digraph sgraph connectivity.
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
Implicit Types c d : seq T.

(** [c] is a cycle (without repetition, of length at least 3) of the relation [r]. *)
Definition seq_cycle c : bool := ucycleb r c && (2 < size c).

(** [c] is a longest cycle of [r]. *)
Definition seq_longest_cycle c : Prop :=
  seq_cycle c /\ forall d, seq_cycle d -> size d <= size c.

End Cycles.

(** ** Definitions copied from GraphLib/cycle.v *)

(** The number of chords of the cycle [c]. *)
Definition cycle_chord_count (G : sgraph) (c : seq G) : nat :=
  #|[set p : G * G |
      [&& p.1 \in c, p.2 \in c, (enum_rank p.1 < enum_rank p.2)%N,
          p.1 -- p.2 & [set p.1; p.2] \notin seq_cycle_edge_list c]]|.

(** ** Statement *)

Definition OPG_3_connected_longest_cycle_chord : Prop :=
  forall (G : sgraph) (c : seq G),
    3.-connected G -> seq_longest_cycle (--) c -> 0 < cycle_chord_count c.
