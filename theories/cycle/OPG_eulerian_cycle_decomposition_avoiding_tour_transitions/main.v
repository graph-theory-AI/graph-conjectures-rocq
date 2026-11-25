(** * Decomposing an eulerian graph into cycles with no two consecutive edges on a prescribed tour

Sabidussi; Open Problem Garden, "Decomposing an eulerian graph into cycles with no two consecutives
edges on a prescribed eulerian tour".

An eulerian tour of a graph is a closed walk that uses every edge exactly once.

Conjecture: let G be an eulerian graph of minimum degree (at least) 4, and let W be an eulerian
tour of G.  Then G admits a decomposition into cycles none of which contains two consecutive edges
of W.

Encoding.  Graphs are multigraphs; loops are allowed and count twice in the degrees.  An eulerian
graph is connected (its underlying simple graph, its "skeleton", is connected).  The tour is the
list of its edges; it is read cyclically: its last edge and its first edge are consecutive.  Cycles
are sets of edges. *)

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

(** [w] is an eulerian tour: a closed walk that uses every edge exactly once. *)
Definition eulerian_tour (G : mgraph) (w : seq (edge G)) : Prop :=
  (exists x : G, uwalk x x w) /\ (forall e : edge G, count (pred1 e) w = 1).

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

End Decompositions.

(** ** Definitions specific to the conjecture *)

(** The pairs of consecutive edges of the closed walk [w] (including its last and first edges). *)
Definition tour_pairs (G : mgraph) (w : seq (edge G)) : seq (edge G * edge G) :=
  zip w (rot 1 w).

(** [C] contains two consecutive edges of the closed walk [w]. *)
Definition two_consecutive (G : mgraph) (w : seq (edge G)) (C : {set edge G}) : bool :=
  has (fun p => (p.1 \in C) && (p.2 \in C)) (tour_pairs w).

(** ** Statement *)

Definition OPG_eulerian_cycle_decomposition_avoiding_tour_transitions : Prop :=
  forall (G : mgraph) (w : seq (edge G)),
    (0 < #|G|)%N -> eulerian G -> (forall v : G, (4 <= mdeg v)%N) ->
    eulerian_tour w ->
    exists D : seq {set edge G},
      cycle_decomposition D /\ (forall C, C \in D -> ~~ two_consecutive w C).
