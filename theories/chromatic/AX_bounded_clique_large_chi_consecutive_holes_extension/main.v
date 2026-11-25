(** * Holes of consecutive lengths in graphs of bounded clique number

Scott, Seymour, "Induced subgraphs of graphs with large chromatic number. IV. Consecutive holes",
J. Combin. Theory B 132 (2018), arXiv:1509.06563, conjectured generalization of Theorem 1.3
(1509.06563__00).

A hole is an induced cycle of length at least 4.

Conjecture: for all integers ν > 0 and k >= 3, there exists n such that if a graph G has no clique
of cardinality k and has chromatic number at least n, then for some t, G has a hole of length t + i
for 1 <= i <= ν.

Encoding.  Graphs are finite and simple.  "No clique of cardinality k" is ω(G) < k. *)

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

Definition AX_bounded_clique_large_chi_consecutive_holes_extension : Prop :=
  forall nu k : nat, 0 < nu -> 3 <= k ->
    exists n : nat, forall G : sgraph,
      ω([set: G]) < k -> n <= χ([set: G]) -> consecutive_holes G nu.
