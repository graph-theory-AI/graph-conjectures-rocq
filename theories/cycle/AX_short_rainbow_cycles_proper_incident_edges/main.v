(** * Short properly coloured cycles

DeVos, Drescher, Funk, González Hermosillo de la Maza, Guo, Huynh, Mohar, Montejano, "Short rainbow
cycles in graphs and matroids", arXiv:1806.00825, Conjecture 4 (1806.00825__00).

A colouring of the edge set E(G) of a graph G is an arbitrary (not necessarily proper) assignment of
colours to the edges.

Conjecture 4: let G be a simple n-vertex graph and let c be a colouring of E(G) with n colours,
where each colour class has size at least r.  Then (G,c) contains a cycle C of length at most
⌈n/r⌉ such that no two incident edges of C have the same colour.

Encoding.  The graph has at least one vertex and r is positive, so that ⌈n/r⌉ makes sense.  The
colouring is defined on all sets of vertices, but only its values on the edges matter.  Cycles are
sequences of vertices. *)

From GraphTheory Require Import digraph sgraph.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

(** The ceiling of [a / b] (0 if [b = 0]). *)
Definition ceil_div (a b : nat) : nat := (a + b - 1) %/ b.

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

(** ** Definitions specific to the conjecture *)

(** Each colour class has at least [r] edges. *)
Definition large_colour_classes (G : sgraph) (n r : nat) (col : {set G} -> 'I_n) : Prop :=
  forall i : 'I_n, r <= #|[set e in E(G) | col e == i]|.

(** Any two distinct edges of the cycle [c] with a common end have distinct colours. *)
Definition properly_coloured_cycle
    (G : sgraph) (n : nat) (col : {set G} -> 'I_n) (c : seq G) : Prop :=
  forall e f : {set G},
    e \in seq_cycle_edge_list c ->
    f \in seq_cycle_edge_list c ->
    e != f ->
    ~~ [disjoint e & f] ->
    col e != col f.

(** ** Statement *)

Definition AX_short_rainbow_cycles_proper_incident_edges : Prop :=
  forall (n r : nat) (G : sgraph) (col : {set G} -> 'I_n),
    0 < n -> 0 < r -> #|G| = n ->
    large_colour_classes r col ->
    exists c : seq G,
      seq_cycle (--) c /\
      size c <= ceil_div n r /\
      properly_coloured_cycle col c.
