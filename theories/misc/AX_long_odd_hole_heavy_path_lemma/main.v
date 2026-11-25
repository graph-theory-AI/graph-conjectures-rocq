(** * Heavy paths in shortest long odd holes

Chudnovsky, Scott, Seymour, "Detecting a long odd hole", arXiv:1904.12273, introduction
(1904.12273__01).

A hole of G is an induced cycle of length at least 4.  For a fixed integer ℓ >= 5, a hole is long
if its length is at least ℓ.  A shortest long odd hole is a long hole of odd length, whose length
is minimum among them.  A vertex v outside of a hole C is C-major if no three-vertex path of C
contains all the neighbours of v in C.

Informal conjecture: for every ℓ >= 5 there is a constant b such that, if C is a shortest long odd
hole of a graph G and M is a set of C-major vertices, one of which is nonadjacent to all the others,
then some path of C of length at most b contains a neighbour of every vertex of M.

Encoding.  "Of bounded length" is read as bounded by a constant that depends only on ℓ.  The paper
needs this extension in its algorithm only, for graphs G that also satisfy other conditions (the
candidates); as in the sentence of the paper, these conditions are not assumed here.  Holes and
paths are sequences of vertices. *)

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

End InducedPathsCycles.
Arguments cyclic_chordless {G} c.
Arguments hole {G} c.

(** ** Definitions specific to the conjecture *)

Section LongOddHoles.
Variable G : sgraph.
Implicit Types (c p : seq G).

(** [c] is a hole of odd length at least [ell]. *)
Definition long_odd_hole (ell : nat) c : Prop := [/\ hole c, odd (size c) & ell <= size c].

(** [c] is a long odd hole of minimum length. *)
Definition shortest_long_odd_hole (ell : nat) c : Prop :=
  long_odd_hole ell c /\ forall d : seq G, long_odd_hole ell d -> size c <= size d.

(** [p] is a path of the cycle [c], with [m] edges where [m < size c]: it consists of [m.+1]
    cyclically consecutive vertices. *)
Definition cycle_path c p : Prop := exists i m, m < size c /\ p = take m.+1 (rot i c).

(** [v] is C-major for the cycle [c]. *)
Definition major c (v : G) : Prop :=
  v \notin c /\
  ~ exists p, [/\ cycle_path c p, size p = 3 & forall u, u \in c -> u -- v -> u \in p].

End LongOddHoles.

(** ** Statement *)

Definition AX_long_odd_hole_heavy_path_lemma : Prop :=
  forall ell : nat, 5 <= ell -> exists b : nat,
    forall (G : sgraph) (c : seq G) (M : {set G}),
      shortest_long_odd_hole ell c ->
      (forall v, v \in M -> major c v) ->
      (exists2 m0, m0 \in M & forall v, v \in M -> v != m0 -> ~~ (m0 -- v)) ->
      exists p, [/\ cycle_path c p, (size p).-1 <= b
                  & forall v, v \in M -> exists2 u, u \in p & v -- u].
