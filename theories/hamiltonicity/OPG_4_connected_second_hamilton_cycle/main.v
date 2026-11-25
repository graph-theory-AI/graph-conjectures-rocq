(** * 4-connected graphs are not uniquely Hamiltonian

Fleischner, "Uniquely Hamiltonian graphs of minimum degree four", J. Graph Theory (2014); Open
Problem Garden, 4_connected_graphs_are_not_uniquely_hamiltonian.

Conjecture: every 4-connected graph with a Hamilton cycle has a second Hamilton cycle.

Encoding.  Graphs are finite and simple.  A 4-connected graph has more than four vertices.  Cycles
are sequences of vertices, and two cycles are distinct if their edge sets are. *)

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

(** The set of the pairs of consecutive elements of the cyclic sequence [c]: the edge set of the
    cycle [c]. *)
Definition seq_cycle_edge_set c : {set {set T}} := [set e in seq_cycle_edge_list c].

End Sequences.

(** ** Definitions copied from GraphLib/hamiltonicity.v *)

(** [c] is a Hamiltonian cycle of [G]. *)
Definition hamiltonian_cycle (G : sgraph) (c : seq G) : bool :=
  ucycleb (--) c && (size c == #|G|).
Arguments hamiltonian_cycle : clear implicits.

(** ** Statement *)

Definition OPG_4_connected_second_hamilton_cycle : Prop :=
  forall G : sgraph, 4.-connected G ->
    forall c : seq G, hamiltonian_cycle G c ->
      exists c' : seq G,
        hamiltonian_cycle G c' /\ seq_cycle_edge_set c' != seq_cycle_edge_set c.
