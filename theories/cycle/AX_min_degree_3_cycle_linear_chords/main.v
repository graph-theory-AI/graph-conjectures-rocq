(** * Cycles with linearly many chords in graphs of minimum degree 3

Dvořák, Martins, Thomassé, Trotignon, "Lollipops, dense cycles and chords", arXiv:2502.04726,
Question 4.3 (2502.04726__03).

A chord of a cycle is an edge joining two non-consecutive vertices of the cycle.

Question 4.3: is there a constant c > 0 such that every graph with minimum degree 3 contains a cycle
of length ℓ with at least cℓ chords?

The proposition states the positive answer.

Encoding.  Graphs are simple and have at least one vertex.  The minimum degree is at least 3, which
is equivalent (deleting edges gives a spanning subgraph of minimum degree 3).  The constant is a
rational number p/q, without loss of generality.  Cycles are sequences of vertices.  Each chord is
counted once, as a pair of vertices whose order is that of their ranks in the enumeration of the
vertices. *)

From GraphTheory Require Import digraph sgraph.
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

(** ** Definitions copied from GraphLib/cycle.v *)

(** The number of chords of the cycle [c]. *)
Definition cycle_chord_count (G : sgraph) (c : seq G) : nat :=
  #|[set p : G * G |
      [&& p.1 \in c, p.2 \in c, (enum_rank p.1 < enum_rank p.2)%N,
          p.1 -- p.2 & [set p.1; p.2] \notin seq_cycle_edge_list c]]|.

(** ** Statement *)

Definition AX_min_degree_3_cycle_linear_chords : Prop :=
  exists p q : nat,
    0 < p /\ 0 < q /\
    forall G : sgraph,
      0 < #|G| ->
      (forall v : G, 3 <= #|N(v)|) ->
      exists c : seq G,
        seq_cycle (--) c /\
        q * cycle_chord_count c >= p * size c.
