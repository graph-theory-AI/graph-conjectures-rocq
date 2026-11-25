(** * Tree-independence number of (even hole, diamond)-free graphs

Abrishami, Alecu, Chudnovsky, Hajebi, Spirkl, Vušković, "Tree independence number I. (Even hole,
diamond, pyramid)-free graphs", J. Graph Theory 106 (2024), arXiv:2305.16258, Conjecture
1.6 (2305.16258__00).

A hole is an induced cycle of length at least 4.  The diamond is K_4 minus an edge.  The
independence number of a tree decomposition is the maximum, over its bags, of the size of a stable
set of the graph contained in the bag.  The tree-independence number of a graph is the minimum
independence number of its tree decompositions.

Conjecture 1.6: the graphs with no even hole and no diamond as an induced subgraph have bounded
tree-independence number.

Encoding.  Graphs are finite and simple. *)

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

(** [G] has an induced subgraph isomorphic to [H]. *)
Definition has_induced_copy (G H : sgraph) : Prop := inhabited (H ⇀ G).

(** The diamond: [K_4] minus an edge. *)
Definition diamond : sgraph := del_edges ([set ord0; ord_max] : {set 'K_4}).

(** ** Definitions copied from GraphLib/minor.v *)

(** The tree-independence number of [G] is at most [k]. *)
Definition tree_independence_le (G : sgraph) (k : nat) : Prop :=
  exists (T : forest) (D : T -> {set G}), sdecomp T G D /\ forall t : T, α(D t) <= k.

(** ** Statement *)

Definition AX_even_hole_diamond_free_tree_independence : Prop :=
  exists k : nat,
    forall G : sgraph,
      even_hole_free G -> ~ has_induced_copy G diamond -> tree_independence_le G k.
