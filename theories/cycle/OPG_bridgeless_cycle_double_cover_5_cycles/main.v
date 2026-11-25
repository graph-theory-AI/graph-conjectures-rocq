(** * (5,2)-cycle covers

Celmins, "On cubic graphs that do not have an edge-3-colouring", Ph.D. thesis, University of
Waterloo (1984); Preissmann; Open Problem Garden, m_n_cycle_covers.

A binary cycle (or even subgraph) of a graph G = (V,E) is a set C of edges such that every vertex
of the graph (V,C) has even degree.  An (m,n)-cycle cover of G is a list of m binary cycles such
that every edge of G is in exactly n of them.

Conjecture (5-cycle double cover): every bridgeless graph has a (5,2)-cycle cover.

Encoding.  Graphs are multigraphs with at least one edge (the other case is trivial), connected or
not.  Loops are allowed: a loop counts twice in the degree of its vertex, and is not a bridge.  The
members of the list may be empty or repeated. *)

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

(** The list of edges [w] is a walk from [x] to [y]; the edges are used in either direction. *)
Fixpoint uwalk (G : mgraph) (x y : G) (w : seq (edge G)) {struct w} : bool :=
  match w with
  | [::] => x == y
  | e :: w' =>
      ((source e == x) && uwalk (target e) y w') ||
      ((target e == x) && uwalk (source e) y w')
  end.

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

Definition OPG_bridgeless_cycle_double_cover_5_cycles : Prop :=
  forall G : mgraph,
    (0 < #|G|)%N -> (0 < #|edge G|)%N -> bridgeless G ->
    exists L : seq {set edge G},
      [/\ size L = 5,
          (forall C, C \in L -> even_subgraph C)
        & (forall e : edge G, count (fun C : {set edge G} => e \in C) L = 2)].
