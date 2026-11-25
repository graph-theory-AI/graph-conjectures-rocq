(** * Treewidth of even-hole-free graphs of bounded degree

Aboulker, Adler, Kim, Sintiari, Trotignon, "On the tree-width of even-hole-free graphs",
arXiv:2008.05504, Conjecture 2 (2008.05504__00).

A hole is an induced cycle of length at least 4.  A graph is even-hole-free if it has no hole of
even length.

Conjecture 2: there is a function f : ℕ -> ℕ such that every even-hole-free graph of maximum
degree at most d has treewidth at most f(d).

Encoding.  Holes are sequences of vertices, and the index graphs of tree decompositions are forests
(this is equivalent to trees). *)

From GraphTheory Require Import digraph sgraph treewidth.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

(** The maximum degree of [G] (0 if [G] is empty). *)
Definition Delta (G : sgraph) : nat := \max_(x : G) #|N(x)|.

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

(** [G] has no hole of even length. *)
Definition even_hole_free : Prop :=
  forall c : seq G,
    hole c ->
    ~~ odd (size c) ->
    False.

End InducedPathsCycles.
Arguments cyclic_chordless {G} c.
Arguments hole {G} c.

(** ** Definitions copied from GraphLib/minor.v *)

(** The treewidth of [G] is at most [k] (the width of a decomposition is, in GraphTheory, the
    maximum size of a bag). *)
Definition treewidth_le (G : sgraph) (k : nat) : Prop :=
  exists (T : forest) (D : T -> {set G}), sdecomp T G D /\ width D <= k.+1.

(** ** Statement *)

Definition AX_even_hole_free_bounded_degree_treewidth : Prop :=
  exists f : nat -> nat,
    forall (d : nat) (G : sgraph),
      Delta G <= d ->
      even_hole_free G ->
      treewidth_le G (f d).
