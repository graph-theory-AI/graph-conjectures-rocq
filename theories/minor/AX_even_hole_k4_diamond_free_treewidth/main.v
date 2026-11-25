(** * Treewidth of (even hole, K_4, diamond)-free graphs

Pilipczuk, Sintiari, Thomassé, Trotignon, "(Theta, triangle)-free and (even hole, K_4)-free graphs.
Part 2: bounds on treewidth", arXiv:2001.01607, open question (2001.01607__00).

A hole is an induced cycle of length at least 4.  The diamond is K_4 minus an edge.  A graph is
(even hole, K_4, diamond)-free if none of its induced subgraphs is a hole of even length, K_4 or
the diamond.

Question: do (even hole, K_4, diamond)-free graphs have bounded treewidth (or cliquewidth)?

Encoding.  Graphs are finite and simple.  The proposition states the positive answer for
treewidth: there is a constant c such that all these graphs have treewidth at most c.  Cliquewidth
is not considered.  (For these graphs, bounding one or the other is equivalent, because they do
not contain K_4,4 as a subgraph: there would be an induced C_4.) *)

From GraphTheory Require Import digraph sgraph treewidth.
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

(** [G] has an induced subgraph isomorphic to [H]. *)
Definition has_induced_copy (G H : sgraph) : Prop := inhabited (H ⇀ G).

(** [G] has no induced subgraph isomorphic to [H]. *)
Definition induced_free (G H : sgraph) : Prop := ~ has_induced_copy G H.

(** The diamond: [K_4] minus an edge. *)
Definition diamond : sgraph := del_edges ([set ord0; ord_max] : {set 'K_4}).

(** ** Definitions copied from GraphLib/minor.v *)

(** The treewidth of [G] is at most [k] (the width of a decomposition is, in GraphTheory, the
    maximum size of a bag). *)
Definition treewidth_le (G : sgraph) (k : nat) : Prop :=
  exists (T : forest) (D : T -> {set G}), sdecomp T G D /\ width D <= k.+1.

(** ** Statement *)

Definition AX_even_hole_k4_diamond_free_treewidth : Prop :=
  exists c : nat,
    forall G : sgraph,
      even_hole_free G -> induced_free G 'K_4 -> induced_free G diamond -> treewidth_le G c.
