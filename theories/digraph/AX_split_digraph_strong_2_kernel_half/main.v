(** * Small strong 2-kernels in split digraphs

Nguyen, Scott, Seymour, "Distant digraph domination", 2024, arXiv:2409.05039, open question on
strong 2-kernels (2409.05039__00).

A set X k-covers a vertex v if there is a directed path of length at most k from a vertex of X to
v.  A 2-kernel of a digraph G is a stable set that 2-covers every vertex.  A source is a vertex of
in-degree zero.  A split digraph is an oriented graph G (without loops and without directed cycles
of length two) whose vertex set has a partition (S,T), called a split, where S is stable and G[T]
is a tournament.  Given a split, a 2-kernel K is strong if each vertex of T is 1-covered by K or
2-covered by K ∩ T.

Question: does every split digraph G with no sources admit a strong 2-kernel of size at most
|G|/2?  The proposition states a positive answer.

Encoding.  Digraphs are those of GraphTheory ([diGraph]: a finite type of vertices with a boolean
relation [--]).  The question is stated for every split (S,T) of the digraph, given by T.  The
vertices that are 1-covered by K are those of the closed out-neighbourhood [NS[K]], and the
vertices that are 2-covered by K are those of [NS[NS[K]]]. *)

From GraphTheory Require Import digraph.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/digraph.v *)

(** [D] is oriented: it has no digon, and no loop. *)
Definition oriented (D : diGraph) : Prop :=
  forall x y : D, x -- y -> ~~ (y -- x).

(** [D] is a tournament: it has no loop, and exactly one arc between any two distinct vertices. *)
Definition tournament (D : diGraph) : Prop :=
  irreflexive (@edge_rel D) /\ forall x y : D, (x != y) = (x -- y) (+) (y -- x).

(** In-degree. *)
Definition indeg (D : diGraph) (v : D) : nat := #|[set u | u -- v]|.

(** There is no arc inside [S]. *)
Definition arc_free (D : diGraph) (S : {set D}) : bool :=
  [forall u in S, [forall v in S, ~~ (u -- v)]].

(** Quasi-kernel, or 2-kernel: an independent set from which each vertex is reached by a directed
    path of length at most 2. *)
Definition quasi_kernel (D : diGraph) (K : {set D}) : Prop :=
  arc_free K /\ forall v : D, v \in NS[NS[K]].

(** ** Definitions specific to the conjecture *)

(** The complement of [T] and [T] form a split of [D]. *)
Definition split_partition (D : diGraph) (T : {set D}) : Prop :=
  arc_free (~: T) /\ tournament (induced T).

(** [K] is a strong 2-kernel of [D] for the split given by [T]. *)
Definition strong_quasi_kernel (D : diGraph) (T K : {set D}) : Prop :=
  quasi_kernel K /\ forall v : D, v \in T -> v \in NS[K] \/ v \in NS[NS[K :&: T]].

(** ** Statement *)

(** A split digraph with no sources has a strong 2-kernel K with |K| <= |D|/2. *)
Definition AX_split_digraph_strong_2_kernel_half : Prop :=
  forall (D : diGraph) (T : {set D}),
    oriented D -> split_partition T -> (forall v : D, 0 < indeg v) ->
    exists K : {set D}, strong_quasi_kernel T K /\ 2 * #|K| <= #|D|.
