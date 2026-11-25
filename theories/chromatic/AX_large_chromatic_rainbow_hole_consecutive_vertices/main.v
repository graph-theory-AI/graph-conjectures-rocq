(** * Holes with many consecutive rainbow vertices

Scott, Seymour, "Induced subgraphs of graphs with large chromatic number. IX. Rainbow paths",
arXiv:1702.01094, concluding question (1702.01094__00).

A hole is an induced cycle of length at least 4.  Given a proper colouring of a graph, a set of
vertices is rainbow if its vertices have pairwise distinct colours.

Question: is it true that for all fixed s and κ, if G is a graph with ω(G) <= κ and χ(G)
sufficiently large, then in every proper colouring of G (not necessarily optimal) there is a hole
in which some set of s consecutive vertices is rainbow?

The proposition states the positive answer.

Encoding.  Graphs are finite and simple.  The s consecutive vertices of a hole c (which has at least
s vertices) are the first s vertices of a rotation of c. *)

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

End InducedPathsCycles.
Arguments cyclic_chordless {G} c.
Arguments hole {G} c.

(** ** Definitions copied from GraphLib/chromatic.v *)

(** [col] is a proper colouring of [G]. *)
Definition proper_coloring (G : sgraph) (C : finType) (col : G -> C) : bool :=
  coloring (preim_partition col [set: G]) [set: G].

(** ** Definitions specific to the conjecture *)

(** For the colouring [col], some hole of [G] has [s] consecutive vertices of distinct colours. *)
Definition rainbow_hole_run
    (G : sgraph) (C : finType) (col : G -> C) (s : nat) : Prop :=
  exists (c : seq G) (r : nat),
    [/\ hole c, s <= size c & uniq (map col (take s (rot r c)))].

(** ** Statement *)

Definition AX_large_chromatic_rainbow_hole_consecutive_vertices : Prop :=
  forall s kappa : nat, exists n : nat,
    forall (G : sgraph) (C : finType) (col : G -> C),
      ω([set: G]) <= kappa ->
      n <= χ([set: G]) ->
      proper_coloring col ->
      rainbow_hole_run col s.
