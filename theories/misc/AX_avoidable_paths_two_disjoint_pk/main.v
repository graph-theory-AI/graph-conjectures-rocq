(** * Two disjoint avoidable paths

Bonamy, Defrain, Hatzel, Thiebaut, "Avoidable paths in graphs", arXiv:1908.03788, Question 1.12
(1908.03788__00).

Cycles are induced, and P_k means an induced path on k vertices.  An extension of an induced path P
is an induced path xPy for some vertices x and y.  An induced path is failing if it is contained in
no induced cycle of G, and avoidable if it has no failing extension.

Question 1.12: for every positive integer k, does every graph G either not contain two disjoint
P_k, or contain two disjoint avoidable P_k?

The proposition states the positive answer.

Encoding.  Paths and cycles are sequences of vertices; disjoint means vertex-disjoint.  An
induced path is contained in an induced cycle if its vertices are. *)

From GraphTheory Require Import digraph sgraph.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

Section Sequences.
Variable T : finType.
Implicit Types s c : seq T.

(** The list of the pairs of consecutive elements of [s]: the edges of a walk. *)
Definition seq_edge_list s : seq {set T} :=
  map (fun e : T * T => [set e.1; e.2]) (zip s (behead s)).

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
Implicit Types (c p : seq G) (u v : G).

(** [p] is an induced path (possibly empty): adjacent vertices of [p] are consecutive. *)
Definition chordless_path p : Prop :=
  [/\ uniq p, sorted (--) p
    & forall u v : G, u \in p -> v \in p -> u -- v -> [set u; v] \in seq_edge_list p].

(** Adjacent vertices of [c] are consecutive in the cyclic sequence [c]. *)
Definition cyclic_chordless c : Prop :=
  forall u v, u \in c -> v \in c -> u -- v -> [set u; v] \in seq_cycle_edge_list c.

(** [c] is an induced cycle (of length at least 3). *)
Definition chordless_cycle c : Prop := seq_cycle (--) c /\ cyclic_chordless c.

End InducedPathsCycles.
Arguments cyclic_chordless {G} c.

(** ** Definitions specific to the conjecture *)

(** [p] is an avoidable path: an induced path such that every extension [u p v] is contained in
    an induced cycle. *)
Definition avoidable_path (G : sgraph) (p : seq G) : Prop :=
  chordless_path p /\
  forall u v : G,
    chordless_path (u :: rcons p v) ->
    exists c : seq G, chordless_cycle c /\ {subset u :: rcons p v <= c}.

(** ** Statement *)

Definition AX_avoidable_paths_two_disjoint_pk : Prop :=
  forall k : nat, 0 < k ->
    forall G : sgraph,
      ~ (exists p q : seq G,
           [/\ size p = k, size q = k, chordless_path p, chordless_path q
             & [disjoint p & q]])
      \/ exists p q : seq G,
           [/\ size p = k, size q = k, avoidable_path p, avoidable_path q & [disjoint p & q]].
