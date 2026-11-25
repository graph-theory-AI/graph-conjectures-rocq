(** * Treewidth of (even hole, K_t)-free graphs

Abrishami, Alecu, Chudnovsky, Hajebi, Spirkl, Vušković, "Tree independence number I. (Even hole,
diamond, pyramid)-free graphs", J. Graph Theory 106 (2024), arXiv:2305.16258, Conjecture
1.7 (2305.16258__01).

A hole is an induced cycle of length at least 4.  A class of graphs has logarithmic treewidth if
there is a constant c such that every graph of the class with n vertices has treewidth at most
c log n.

Conjecture 1.7: for every t, the class of graphs with no even hole and no clique on t vertices has
logarithmic treewidth.

Encoding.  Graphs are finite and simple.  The constant c depends on t.  The bound c log n is
replaced by c (1 + ⌊log_2 n⌋), which is equivalent up to the choice of c.  "No clique on t vertices"
means that the clique number is less than t. *)

From GraphTheory Require Import digraph sgraph coloring treewidth.
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

Definition AX_even_hole_kt_free_logarithmic_treewidth : Prop :=
  forall t : nat, exists c : nat,
    forall G : sgraph,
      even_hole_free G -> ω([set: G]) < t ->
      treewidth_le G (c * (trunc_log 2 #|G|).+1).
