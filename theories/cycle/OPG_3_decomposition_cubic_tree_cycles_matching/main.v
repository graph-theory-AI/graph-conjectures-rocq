(** * The 3-decomposition conjecture

Hoffmann-Ostenhof; Open Problem Garden, 3_decomposition_conjecture.

A graph is cubic if all its degrees are 3.  A matching is a set of edges that have pairwise no
common end.  A decomposition of a graph is a partition of its edge set.

Conjecture: every connected cubic graph has a decomposition into a spanning tree, a family of
cycles and a matching.  More precisely, its edge set is the disjoint union of the edge sets of a
spanning tree, of a 2-regular subgraph and of a matching, where only the matching may be empty.

Encoding.  Graphs are the finite multigraphs of GraphTheory: parallel edges are allowed (two
parallel edges form a cycle) and loops are excluded.  The reference direction of the edges plays
no role.  The empty graph is excluded.  The 2-regular subgraph F is automatically nonempty: for n
vertices, the tree has n-1 of the 3n/2 edges and the matching at most n/2. *)

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

(** ** Definitions copied from GraphLib/packing.v *)

(** [M] is a matching of the multigraph [G] (without loops). *)
Definition mmatching (G : mgraph) (M : {set edge G}) : Prop :=
  forall v : G, (mdeg_in M v <= 1)%N.

(** ** Definitions copied from GraphLib/cycle.v *)

Section EdgeSets.
Variable G : mgraph.
Implicit Types C H T : {set edge G}.

(** [H] contains no cycle. *)
Definition acyclic_edge_set H : Prop :=
  forall C : {set edge G}, C \subset H -> ~ is_circuit C.

(** The spanning subgraph with edge set [T] is connected. *)
Definition spanning_connected T : Prop :=
  connected [set: skeleton.skeleton (remove_edges (~: T))].

(** [T] is the edge set of a spanning tree. *)
Definition mspanning_tree T : Prop :=
  spanning_connected T /\ acyclic_edge_set T.

End EdgeSets.

Section Decompositions.
Variable G : mgraph.
Implicit Types (C : {set edge G}) (D : seq {set edge G}).

(** Each edge is in exactly one member of [D]. *)
Definition medge_partition D : Prop :=
  forall e : edge G, count (fun C : {set edge G} => e \in C) D = 1.

End Decompositions.

(** ** Statement *)

Definition OPG_3_decomposition_cubic_tree_cycles_matching : Prop :=
  forall G : mgraph,
    0 < #|G| -> loopless_cubic G -> connected [set: skeleton.skeleton G] ->
    exists T F M : {set edge G},
      [/\ mspanning_tree T, subgraph_kregular F 2, mmatching M
        & medge_partition [:: T; F; M]].
