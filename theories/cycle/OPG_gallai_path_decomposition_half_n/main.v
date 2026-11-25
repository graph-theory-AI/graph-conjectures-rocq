(** * Decomposing a connected graph into paths

Gallai, see Lovász, "On covering of graphs", Theory of Graphs (Proc. Colloq., Tihany, 1966),
Academic Press (1968), 231-236; Open Problem Garden, decomposing_a_connected_graph_into_paths.

Conjecture: every simple connected graph on n vertices can be decomposed into at most (n+1)/2
paths.

Encoding.  A simple graph is a multigraph without loops and parallel edges.  It is assumed to have
at least one edge, which only excludes the trivial case of one vertex.  Paths are sets of edges: a
path is a nonempty set of edges that is connected, contains no cycle, and where all degrees are at
most 2.  The bound is replaced by its integer part. *)

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

Section EdgeSets.
Variable G : mgraph.
Implicit Types C H P : {set edge G}.

(** [H] contains no cycle. *)
Definition acyclic_edge_set H : Prop :=
  forall C : {set edge G}, C \subset H -> ~ is_circuit C.

(** [P] is the edge set of a path with at least one edge. *)
Definition path_subgraph P : Prop :=
  [/\ P != set0, subgraph_connected P, acyclic_edge_set P & forall v : G, (mdeg_in P v <= 2)%N].

End EdgeSets.

Section Decompositions.
Variable G : mgraph.
Implicit Types (C : {set edge G}) (D : seq {set edge G}).

(** Each edge is in exactly one member of [D]. *)
Definition medge_partition D : Prop :=
  forall e : edge G, count (fun C : {set edge G} => e \in C) D = 1.

(** [D] is a decomposition of [G] into paths. *)
Definition mpath_decomposition D : Prop :=
  (forall P, P \in D -> path_subgraph P) /\ medge_partition D.

End Decompositions.

(** ** Statement *)

Definition OPG_gallai_path_decomposition_half_n : Prop :=
  forall G : mgraph,
    (0 < #|G|)%N -> (0 < #|edge G|)%N -> msimple G ->
    connected [set: skeleton.skeleton G] ->
    exists D : seq {set edge G},
      mpath_decomposition D /\ (size D <= (#|G| + 1) %/ 2)%N.
