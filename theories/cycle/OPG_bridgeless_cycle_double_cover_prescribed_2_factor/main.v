(** * Cycle double covers containing predefined 2-regular subgraphs

Hoffmann-Ostenhof; Open Problem Garden,
cycle_double_covers_containing_predefined_2_regular_subgraphs.

A cycle is a connected 2-regular subgraph.  A cycle double cover of a graph G is a set of cycles of
G such that every edge of G is in exactly two of them.

Conjecture: let G be a 2-connected cubic graph and let S be a 2-regular subgraph of G such that
G - E(S) is connected.  Then G has a cycle double cover which contains S (i.e. all cycles of S).

Encoding.  Graphs are loopless multigraphs.  A 2-connected graph has at least three vertices here,
which excludes only the graph with two vertices joined by three edges.  Connectivity notions are
those of the underlying simple graph ("skeleton").  Subgraphs and cycles are sets of edges.  S is
not necessarily spanning, and may be empty.  All vertices of G are kept in G - E(S).  A cycle double
cover is a list of cycles (which has no repetition when G is cubic).  It contains S if it contains
all members of some decomposition of S into cycles (which is unique up to the order). *)

From GraphTheory Require Import mgraph.
From GraphTheory Require Import digraph sgraph connectivity.
From GraphTheory Require skeleton.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

(** Multigraphs without labels. *)
Abbreviation mgraph := (graph unit unit).

(** [G] has no loop. *)
Definition mloopless (G : mgraph) : Prop := forall e : edge G, source e != target e.

(** Every vertex is incident to [r] edges (a loop is counted once). *)
Definition mregular (G : mgraph) (r : nat) : Prop := forall v : G, #|edges_at v| = r.

(** Every vertex is incident to three edges (a loop is counted once). *)
Definition mcubic (G : mgraph) : Prop := mregular G 3.

(** [G] is cubic and has no loop. *)
Definition loopless_cubic (G : mgraph) : Prop := mloopless G /\ mcubic G.

(** The degree of [v] in the edge set [H] (a loop is counted twice). *)
Definition mdeg_in (G : mgraph) (H : {set edge G}) (v : G) : nat :=
  #|[set e in H | source e == v]| + #|[set e in H | target e == v]|.

(** [H] is the edge set of a [k]-regular subgraph. *)
Definition subgraph_kregular (G : mgraph) (H : {set edge G}) (k : nat) : Prop :=
  forall v : G, mdeg_in H v = 0 \/ mdeg_in H v = k.

(** The list of edges [w] is a walk from [x] to [y]; the edges are used in either direction. *)
Fixpoint uwalk (G : mgraph) (x y : G) (w : seq (edge G)) {struct w} : bool :=
  match w with
  | [::] => x == y
  | e :: w' =>
      ((source e == x) && uwalk (target e) y w') ||
      ((target e == x) && uwalk (source e) y w')
  end.

(** [w] is a walk from [x] to [y] with edges in [H]. *)
Definition uwalk_in (G : mgraph) (H : {set edge G}) (x y : G) (w : seq (edge G)) : bool :=
  uwalk x y w && all (fun e => e \in H) w.

(** The vertex [x] is an end of an edge of [H]. *)
Definition subgraph_incident (G : mgraph) (H : {set edge G}) (x : G) : bool :=
  [exists e, (e \in H) && incident x e].

(** The subgraph with edge set [H] and without isolated vertices is connected. *)
Definition subgraph_connected (G : mgraph) (H : {set edge G}) : Prop :=
  forall x y : G, subgraph_incident H x -> subgraph_incident H y -> exists w, uwalk_in H x y w.

(** [C] is the edge set of a cycle of [G] (a loop and a pair of parallel edges are cycles). *)
Definition is_circuit (G : mgraph) (C : {set edge G}) : Prop :=
  [/\ C != set0, subgraph_kregular C 2 & subgraph_connected C].

(** ** Definitions copied from GraphLib/cycle.v *)

Section Decompositions.
Variable G : mgraph.
Implicit Types (C H : {set edge G}) (D L : seq {set edge G}).

(** [L] is a faithful cycle cover for the weights [p]: each edge [e] is in exactly [p e] cycles
    of [L]. *)
Definition faithful_cycle_cover (p : edge G -> nat) L : Prop :=
  (forall C, C \in L -> is_circuit C) /\
  (forall e : edge G, count (fun C : {set edge G} => e \in C) L = p e).

(** [D] is a decomposition of [H] into cycles: each edge of [H] is in exactly one cycle of [D], and
    the other edges are in none. *)
Definition cycle_decomposition_of H D : Prop := faithful_cycle_cover (fun e => e \in H) D.

(** [L] is a cycle double cover: each edge is in exactly two cycles of [L]. *)
Definition cycle_double_cover L : Prop := faithful_cycle_cover (fun=> 2) L.

End Decompositions.

(** ** Statement *)

Definition OPG_bridgeless_cycle_double_cover_prescribed_2_factor : Prop :=
  forall (G : mgraph) (S : {set edge G}),
    (0 < #|G|)%N -> loopless_cubic G -> kconnected 2 (skeleton.skeleton G) ->
    subgraph_kregular S 2 -> connected [set: skeleton.skeleton (remove_edges S)] ->
    exists L : seq {set edge G},
      cycle_double_cover L /\
      exists D : seq {set edge G},
        cycle_decomposition_of S D /\ {subset D <= L}.
