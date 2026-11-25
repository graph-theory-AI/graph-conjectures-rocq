(** * Acyclic edge colouring

Fiamčík (1978); Open Problem Garden, acyclic_edge_coloring.

Conjecture: every simple graph of maximum degree Δ has a proper edge colouring with Δ + 2 colours
such that every cycle contains edges of at least three distinct colours.

Encoding.  Graphs are finite.  An edge colouring is a map on the sets of vertices, whose values on
the sets that are not edges are irrelevant.  Cycles are cyclic sequences of at least 3 distinct
vertices. *)

From GraphTheory Require Import digraph sgraph.
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

(** ** Definitions copied from GraphLib/chromatic.v *)

(** [col] is a proper edge colouring. *)
Definition proper_edge_coloring (G : sgraph) (C : eqType) (col : {set G} -> C) : Prop :=
  forall x y z : G, x -- y -> x -- z -> y != z -> col [set x; y] != col [set x; z].

(** [col] is an acyclic edge colouring: it is proper, and each cycle has at least three
    colours. *)
Definition acyclic_edge_coloring (G : sgraph) (k : nat) (col : {set G} -> 'I_k) : Prop :=
  proper_edge_coloring col /\
  forall s : seq G, seq_cycle (--) s -> 2 < size (undup (map col (seq_cycle_edge_list s))).

(** ** Statement *)

Definition OPG_acyclic_edge_coloring_delta_plus_2 : Prop :=
  forall G : sgraph,
    exists col : {set G} -> 'I_(Delta G + 2), acyclic_edge_coloring col.
