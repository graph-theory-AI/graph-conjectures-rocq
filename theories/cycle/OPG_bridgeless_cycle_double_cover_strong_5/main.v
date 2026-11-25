(** * Strong 5-cycle double cover conjecture

Hoffmann-Ostenhof; Open Problem Garden, strong_5_cycle_double_cover_conjecture.

A circuit is a connected 2-regular subgraph.  A cycle is here a 2-regular subgraph, not necessarily
connected.  A five cycle double cover of a graph G is a list of five cycles of G such that every
edge of G is in exactly two of them.

Conjecture: let C be a circuit in a bridgeless cubic graph G.  Then there is a five cycle double
cover of G such that C is a subgraph of one of these five cycles.

Encoding.  Graphs are multigraphs.  They are loopless (a cubic graph with a loop has a bridge) and
need not be connected.  Circuits and cycles are sets of edges.  Cycles are encoded as even
subgraphs (all degrees are even), which is the same notion in a cubic graph.  The five cycles may
be empty or repeated. *)

From GraphTheory Require Import mgraph.
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

(** [e] is a bridge: every walk between its ends uses it. *)
Definition mbridge (G : mgraph) (e : edge G) : Prop :=
  forall w : seq (edge G), uwalk (source e) (target e) w -> e \in w.

(** [G] has no bridge. *)
Definition bridgeless (G : mgraph) : Prop :=
  forall e : edge G, ~ mbridge e.

(** ** Definitions copied from GraphLib/cycle.v *)

Section EdgeSets.
Variable G : mgraph.
Implicit Types C : {set edge G}.

(** [C] is an even subgraph: all its degrees are even. *)
Definition even_subgraph C : Prop :=
  forall v : G, ~~ odd (mdeg_in C v).

End EdgeSets.

(** ** Statement *)

Definition OPG_bridgeless_cycle_double_cover_strong_5 : Prop :=
  forall (G : mgraph) (C : {set edge G}),
    (0 < #|G|)%N -> loopless_cubic G -> bridgeless G -> is_circuit C ->
    exists L : seq {set edge G},
      [/\ size L = 5,
          (forall D, D \in L -> even_subgraph D),
          (forall e : edge G, count (fun D : {set edge G} => e \in D) L = 2)
        & (exists D, D \in L /\ C \subset D)].
