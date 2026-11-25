(** * Long directed cycles in oriented graphs of given minimum in- and out-degree

Jackson, "Long paths and cycles in oriented graphs", J. Graph Theory 5 (1981); Open Problem Garden,
long_directed_cycles_in_digraph_with_minimum_in_and_out_degree.

An oriented graph is a digraph without loop and without digon.

Conjecture: every strong oriented graph in which each vertex has in-degree and out-degree at least d
contains a directed cycle of length at least 2d + 1.

Encoding.  Digraphs are those of GraphTheory ([diGraph]): a finite type of vertices with a boolean
relation [--].  The digraph is nonempty and d is positive, which is implicit in the source (for
d = 0, a single vertex has no directed cycle).  A directed cycle is given by the sequence of its
vertices. *)

From GraphTheory Require Import digraph.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/digraph.v *)

(** [D] is oriented: it has no digon, and no loop. *)
Definition oriented (D : diGraph) : Prop :=
  forall x y : D, x -- y -> ~~ (y -- x).

(** Out-degree. *)
Definition outdeg (D : diGraph) (v : D) : nat := #|N(v)|.

(** In-degree. *)
Definition indeg (D : diGraph) (v : D) : nat := #|[set u | u -- v]|.

(** The minimum in-degree and the minimum out-degree of [D] are at least [k]. *)
Definition min_semidegree_ge (D : diGraph) (k : nat) : Prop :=
  forall v : D, (k <= outdeg v)%N /\ (k <= indeg v)%N.

(** The vertices [c] form a directed cycle, of length [size c] (a loop or a digon is one). *)
Definition dicycle (D : diGraph) (c : seq D) : bool := ~~ nilp c && ucycleb (--) c.

(** [D] is strongly connected. *)
Definition strongly_connected (D : diGraph) : bool :=
  [forall x : D, forall y : D, connect (--) x y].

(** ** Statement *)

Definition OPG_oriented_in_out_degree_long_cycle : Prop :=
  forall (D : diGraph) (d : nat), oriented D -> 0 < #|D| -> 0 < d ->
    strongly_connected D -> min_semidegree_ge D d ->
    exists c : seq D, dicycle c /\ 2 * d + 1 <= size c.
