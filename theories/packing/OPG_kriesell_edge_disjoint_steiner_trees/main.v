(** * Kriesell's conjecture

Kriesell; Open Problem Garden, kriesells_conjecture; Bondy, Murty, "Graph Theory", Appendix A,
problem 22.

Conjecture: let G be a graph and let T be a set of vertices such that for any two vertices u and v
of T there are 2k edge-disjoint paths from u to v in G.  Then G contains k edge-disjoint trees, each
of which contains T.

Encoding.  Graphs are the finite multigraphs of GraphTheory: loops and parallel edges are allowed,
and the reference direction of the edges plays no role.  Edge-disjoint walks are used instead of
edge-disjoint paths, which is equivalent.  A tree is given by its edge set, which is connected and
contains no cycle (a loop and a pair of parallel edges are cycles).  It contains T if any two
vertices of T are joined by a walk using its edges; if T has at most one vertex, the tree may
have no edge. *)

From GraphTheory Require Import mgraph.
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

(** There are [k] edge-disjoint walks from [x] to [y], or, equivalently, [k] edge-disjoint paths
    ([x] and [y] are meant to be distinct). *)
Definition medge_disjoint_paths (G : mgraph) (x y : G) (k : nat) : Prop :=
  exists ws : seq (seq (edge G)),
    [/\ size ws = k,
        (forall w : seq (edge G), w \in ws -> uwalk x y w)
      & (forall e : edge G, count (fun w : seq (edge G) => e \in w) ws <= 1)].

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

Section EdgeSets.
Variable G : mgraph.
Implicit Types C H : {set edge G}.

(** [H] contains no cycle. *)
Definition acyclic_edge_set H : Prop :=
  forall C : {set edge G}, C \subset H -> ~ is_circuit C.

End EdgeSets.

(** ** Definitions specific to the conjecture *)

(** [H] is the edge set of a tree that contains [T]. *)
Definition tree_containing (G : mgraph) (T : {set G}) (H : {set edge G}) : Prop :=
  [/\ acyclic_edge_set H, subgraph_connected H
    & forall x y : G, x \in T -> y \in T -> exists w : seq (edge G), uwalk_in H x y w].

(** ** Statement *)

Definition OPG_kriesell_edge_disjoint_steiner_trees : Prop :=
  forall (G : mgraph) (T : {set G}) (k : nat),
    (forall u v : G, u \in T -> v \in T -> u != v -> medge_disjoint_paths u v (2 * k)) ->
    exists Hs : seq {set edge G},
      [/\ size Hs = k,
          (forall H : {set edge G}, H \in Hs -> tree_containing T H)
        & (forall e : edge G, count (fun H : {set edge G} => e \in H) Hs <= 1)].
