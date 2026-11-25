(** * Decomposing an eulerian graph into cycles

Hajós, see Lovász, "On covering of graphs", Theory of Graphs (Proc. Colloq., Tihany, 1966), Academic
Press (1968), 231-236; Open Problem Garden, decomposing_an_eulerian_graph_into_cycles.

Conjecture: every simple eulerian graph on n vertices can be decomposed into at most (n-1)/2
cycles.

Encoding.  A simple graph is a multigraph without loops and parallel edges.  It is assumed to have
at least one edge, which only excludes the trivial case of one vertex.  An eulerian graph is a
connected graph with even degrees.  Cycles are sets of edges.  The bound is replaced by its integer
part. *)

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

(** ** Definitions copied from GraphLib/chromatic.v *)

(** [G] has no loop and no parallel edges. *)
Definition msimple (G : mgraph) : Prop :=
  mloopless G /\ injective (fun e : edge G => [set source e; target e]).

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

End Decompositions.

(** ** Statement *)

Definition OPG_eulerian_cycle_decomposition_hajos_n_half : Prop :=
  forall G : mgraph,
    (0 < #|G|)%N -> (0 < #|edge G|)%N -> msimple G -> eulerian G ->
    exists D : seq {set edge G},
      cycle_decomposition D /\ (size D <= (#|G| - 1) %/ 2)%N.
