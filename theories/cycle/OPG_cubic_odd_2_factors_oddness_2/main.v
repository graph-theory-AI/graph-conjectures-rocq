(** * Odd cycles and low oddness

Open Problem Garden, odd_cycles_and_low_oddness.

A 2-factor of a graph G is a spanning 2-regular subgraph.  The oddness ω(G) of G is the minimum
number of odd cycles in a 2-factor of G.

Conjecture: if in a bridgeless cubic graph G the cycles of any 2-factor are odd, then ω(G) <= 2.

Encoding.  Graphs are multigraphs.  They are loopless (a cubic graph with a loop has a bridge).
Subgraphs are sets of edges.  "ω(G) <= 2" is expressed by the existence of a 2-factor with a
decomposition into cycles, at most two of which are odd.
G is required to be connected (that is, its underlying simple graph, its "skeleton", is connected),
which is implicit in the source: oddness is additive over components, and for instance every
2-factor of the disjoint union of two Petersen graphs consists of four cycles of length 5. *)

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
Implicit Types F : {set edge G}.

(** [F] is the edge set of a 2-factor. *)
Definition two_factor F : Prop :=
  forall v : G, mdeg_in F v = 2.

End EdgeSets.

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

End Decompositions.

(** The oddness of [G] (minimum number of odd cycles of a 2-factor) is at most [k]. *)
Definition oddness_le (G : mgraph) (k : nat) : Prop :=
  exists (F : {set edge G}) (D : seq {set edge G}),
    [/\ two_factor F, cycle_decomposition_of F D
      & (count (fun C : {set edge G} => odd #|C|) D <= k)%N].

(** ** Statement *)

Definition OPG_cubic_odd_2_factors_oddness_2 : Prop :=
  forall G : mgraph,
    (0 < #|G|)%N -> loopless_cubic G -> connected [set: skeleton.skeleton G] -> bridgeless G ->
    (forall F : {set edge G}, two_factor F ->
       forall C : {set edge G}, C \subset F -> is_circuit C -> odd #|C|) ->
    oddness_le G 2.
