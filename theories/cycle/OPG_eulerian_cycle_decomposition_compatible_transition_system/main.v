(** * Decomposing eulerian graphs

Open Problem Garden, decomposing_eulerian_graphs.

Let G be an eulerian graph.  A transition system P for G gives, for each vertex v, a partition P(v)
of the edges incident with v.  It is a 2-transition system if every member of every P(v) has size
at most 2.  A compatible decomposition of (G,P) is a list of edge-disjoint cycles with union G, such
that each of these cycles contains at most one edge from every member of P(v), for each v.

Conjecture: if G is a 6-edge-connected eulerian graph and P is a 2-transition system for G, then
(G,P) has a compatible decomposition.

Encoding.  Graphs are multigraphs with at least one edge.  Connectivity is that of the underlying
simple graph ("skeleton").  Cycles are sets of edges.  Loops are allowed and count twice in the
degrees, but P(v) is a partition of the set of edges at v, where a loop occurs once.  The members
of P(v) are required to have size exactly 2, and a cycle C is compatible with P if, for each v, the
set of its edges at v is not a member of P(v).  This is equivalent: loops can be removed from G and
P (each of them is a cycle, with a single edge), then the number of members of size 1 of P(v) is
even, and merging them in pairs only adds constraints; moreover, a cycle through v has exactly two
edges at v, unless it is a loop. *)

From GraphTheory Require Import mgraph.
From GraphTheory Require Import digraph sgraph.
From GraphTheory Require skeleton.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

(** Multigraphs without labels. *)
Abbreviation mgraph := (graph unit unit).

(** The degree of [v] in the edge set [H] (a loop is counted twice). *)
Definition mdeg_in (G : mgraph) (H : {set edge G}) (v : G) : nat :=
  #|[set e in H | source e == v]| + #|[set e in H | target e == v]|.

(** The degree of [v] (a loop is counted twice). *)
Definition mdeg (G : mgraph) (v : G) : nat := mdeg_in [set: edge G] v.

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

(** [G] is [k]-edge-connected: it remains connected when fewer than [k] edges are deleted. *)
Definition medge_connected (G : mgraph) (k : nat) : Prop :=
  forall E : {set edge G}, #|E| < k -> connected [set: skeleton.skeleton (remove_edges E)].

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

(** [G] is eulerian: it is connected (possibly empty) and all degrees are even. *)
Definition eulerian (G : mgraph) : Prop :=
  connected [set: skeleton.skeleton G] /\ forall v : G, ~~ odd (mdeg v).

Section Decompositions.
Variable G : mgraph.
Implicit Types (C : {set edge G}) (D L : seq {set edge G}).

(** [L] is a faithful cycle cover for the weights [p]: each edge [e] is in exactly [p e] cycles
    of [L]. *)
Definition faithful_cycle_cover (p : edge G -> nat) L : Prop :=
  (forall C, C \in L -> is_circuit C) /\
  (forall e : edge G, count (fun C : {set edge G} => e \in C) L = p e).

(** [D] is a decomposition of [G] into cycles. *)
Definition cycle_decomposition D : Prop := faithful_cycle_cover (fun=> 1) D.

(** A transition system: a partition of the edges around each vertex into pairs. *)
Definition transition_system (P : G -> {set {set edge G}}) : Prop :=
  (forall v : G, partition (P v) (edges_at v)) /\
  (forall (v : G) (T : {set edge G}), T \in P v -> #|T| = 2).

(** [D] is a cycle decomposition compatible with the transition system [P]: the two edges of a
    cycle around a vertex are not a pair of [P]. *)
Definition compatible_decomposition (P : G -> {set {set edge G}}) D : Prop :=
  cycle_decomposition D /\
  (forall C, C \in D -> forall v : G, (edges_at v :&: C) \notin P v).

End Decompositions.

(** ** Statement *)

Definition OPG_eulerian_cycle_decomposition_compatible_transition_system : Prop :=
  forall (G : mgraph) (P : G -> {set {set edge G}}),
    (0 < #|G|)%N -> (0 < #|edge G|)%N -> medge_connected G 6 -> eulerian G ->
    transition_system P ->
    exists D : seq {set edge G}, compatible_decomposition P D.
