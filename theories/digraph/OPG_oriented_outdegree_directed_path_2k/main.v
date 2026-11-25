(** * Directed path of length twice the minimum out-degree

Thomassé; Open Problem Garden, directed_cycle_of_length_twice_the_minimum_outdegree.

An oriented graph is a digraph without loop or digon.

Conjecture: every oriented graph with minimum out-degree k contains a directed path of length 2k.

Encoding.  Oriented graphs are digraphs of GraphTheory ([diGraph]: a finite type of vertices with a
boolean relation [--]) satisfying the predicate [oriented].  They are assumed to have a vertex.  The
length of a path is its number of arcs.  The minimum out-degree is assumed to be at least k, which
is equivalent. *)

From GraphTheory Require Import digraph.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

Section Paths.
Variable G : diGraph.
Implicit Types p : seq G.

(** [p] is a path (nonempty, without repetition). *)
Definition seq_simple_path p : bool := if p is x :: q then path (--) x q && uniq p else false.

End Paths.

(** ** Definitions copied from GraphLib/digraph.v *)

(** [D] is oriented: it has no digon, and no loop. *)
Definition oriented (D : diGraph) : Prop :=
  forall x y : D, x -- y -> ~~ (y -- x).

(** Out-degree. *)
Definition outdeg (D : diGraph) (v : D) : nat := #|N(v)|.

(** The minimum out-degree of [D] is at least [k]. *)
Definition min_outdeg_ge (D : diGraph) (k : nat) : Prop := forall v : D, (k <= outdeg v)%N.

(** The vertices [x :: s] form a directed path (from [x] to [last x s], of length [size s]). *)
Definition dipath (D : diGraph) (x : D) (s : seq D) : bool := seq_simple_path (x :: s).

(** [D] has a directed path of length [k]. *)
Definition has_dipath (D : diGraph) (k : nat) : bool :=
  [exists x : D, exists t : k.-tuple D, dipath x t].

(** ** Statement *)

Definition OPG_oriented_outdegree_directed_path_2k : Prop :=
  forall (D : diGraph) (k : nat), oriented D -> 0 < #|D| -> min_outdeg_ge D k ->
    has_dipath D (2 * k).
