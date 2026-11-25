(** * Geodesic cycles and Tutte's theorem

Georgakopoulos, Sprüssel, "Geodesic topological cycles in locally finite graphs", Electron. J.
Combin. 16 (2009); Open Problem Garden, geodesic_cycles_and_tuttes_theorem.

Let ℓ assign a positive length to each edge of a graph G.  A cycle C of G is ℓ-geodesic if, for
every two vertices x and y of C, no path from x to y in G is shorter, with respect to ℓ, than both
paths from x to y on C.  A cycle is peripheral if it is induced and deleting its vertices leaves a
connected graph.

Question: if G is a finite 3-connected graph, is there an assignment ℓ of positive lengths such that
every ℓ-geodesic cycle of G is peripheral?  What is stated is the positive answer.

Encoding.  Lengths are in an arbitrary ordered field.  This is equivalent to real lengths, as the
conditions on ℓ are linear inequalities with integer coefficients.  Cycles are sequences of at least
three vertices.  A cycle C is ℓ-geodesic if, for any two vertices u and v of C, some walk from u to
v with all its edges on C has the minimum length among all walks from u to v in G. *)

From GraphTheory Require Import digraph sgraph connectivity.
From mathcomp Require Import boot order algebra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.Theory GRing.Theory Num.Theory.

(** ** Definitions copied from GraphLib/misc.v *)

Section Sequences.
Variable T : finType.
Implicit Types (s c : seq T).

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
Implicit Types (c : seq G) (u v : G).

(** Adjacent vertices of [c] are consecutive in the cyclic sequence [c]. *)
Definition cyclic_chordless c : Prop :=
  forall u v, u \in c -> v \in c -> u -- v -> [set u; v] \in seq_cycle_edge_list c.

(** [c] is an induced cycle (of length at least 3). *)
Definition chordless_cycle c : Prop := seq_cycle (--) c /\ cyclic_chordless c.

End InducedPathsCycles.
Arguments cyclic_chordless {G} c.

(** ** Definitions copied from GraphLib/extremal.v *)

(** [c] is a peripheral cycle: an induced cycle whose deletion leaves a connected graph. *)
Definition peripheral_cycle (G : sgraph) (c : seq G) : Prop :=
  chordless_cycle c /\ connected (~: [set x in c]).

(** ** Definitions specific to the conjecture *)

Section EdgeLengths.
Variables (R : realFieldType) (G : sgraph) (ell : {set G} -> R).

(** The length of the walk [u :: p]: the sum of the lengths of its edges. *)
Definition walk_weight (u : G) (p : seq G) : R :=
  (\sum_(e <- seq_edge_list (u :: p)) ell e)%R.

(** [u :: p] is a walk from [u] to [v] of minimum length. *)
Definition shortest_walk (u v : G) (p : seq G) : Prop :=
  [/\ path (--) u p, last u p = v &
      forall q : seq G, path (--) u q -> last u q = v -> (walk_weight u p <= walk_weight u q)%R].

(** [c] is a geodesic cycle: any two of its vertices are joined by a shortest walk with edges
    on [c]. *)
Definition geodesic_cycle (c : seq G) : Prop :=
  seq_cycle (--) c /\
  forall u v : G, u \in c -> v \in c ->
    exists p : seq G, shortest_walk u v p /\
      {subset seq_edge_list (u :: p) <= seq_cycle_edge_list c}.

End EdgeLengths.

(** ** Statement *)

Definition OPG_3_connected_geodesic_cycles_peripheral_lengths : Prop :=
  forall (R : realFieldType) (G : sgraph),
    3.-connected G ->
    exists ell : {set G} -> R,
      (forall e : {set G}, e \in E(G) -> (0 < ell e)%R) /\
      (forall c : seq G, geodesic_cycle ell c -> peripheral_cycle c).
