(** * Holes of consecutive lengths in graphs of large chromatic number

Scott, Seymour, "Induced subgraphs of graphs with large chromatic number. X. Holes of specific
residue", arXiv:1705.04609, Conjecture 1.8 (1705.04609__00).

A hole is an induced cycle of length at least 4.  Holes of l consecutive lengths are holes of
lengths k, k + 1, ..., k + l - 1 for some k.

Conjecture 1.8: for all integers κ, l >= 0, there exists c >= 0 such that every graph with chromatic
number greater than c contains either a complete subgraph on κ vertices or holes of l consecutive
lengths.

Encoding.  Graphs are finite and simple.  "A complete subgraph on κ vertices" is κ <= ω(G). *)

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

(** [G] has holes of [l] consecutive lengths. *)
Definition consecutive_holes (l : nat) : Prop :=
  exists t : nat, forall i : nat, 1 <= i -> i <= l -> has_hole_of_length (t + i).

End InducedPathsCycles.
Arguments cyclic_chordless {G} c.
Arguments hole {G} c.

(** ** Statement *)

Definition AX_bounded_clique_large_chi_consecutive_holes : Prop :=
  forall kappa ell : nat, exists c : nat,
    forall G : sgraph,
      c < χ([set: G]) ->
      kappa <= ω([set: G]) \/ consecutive_holes G ell.
