(** * Stable set meeting all longest directed paths

Laborde, Payan, Xuong, "Independent sets and longest directed paths in digraphs", Graphs and other
Combinatorial Topics (Prague, 1982); Open Problem Garden,
stable_set_meeting_all_longest_directed_paths.

A set of vertices is stable if there is no arc between two of its vertices.

Conjecture: every digraph has a stable set that meets all directed paths of maximum length.

Encoding.  Digraphs are those of GraphTheory ([diGraph]): a finite type of vertices with a boolean
relation [--], without loop here (a vertex with a loop is in no stable set).  Digons are allowed.
A directed path is given by its first vertex and the sequence of the other ones. *)

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

(** The vertices [x :: s] form a directed path (from [x] to [last x s], of length [size s]). *)
Definition dipath (D : diGraph) (x : D) (s : seq D) : bool := seq_simple_path (x :: s).

(** [D] has a directed path of length [k]. *)
Definition has_dipath (D : diGraph) (k : nat) : bool :=
  [exists x : D, exists t : k.-tuple D, dipath x t].

(** The maximum length of a directed path of [D] (0 if [D] is empty). *)
Definition longest_dipath_length (D : diGraph) : nat :=
  \max_(k < #|D| | has_dipath D k) (k : nat).

(** There is no arc inside [S]. *)
Definition arc_free (D : diGraph) (S : {set D}) : bool :=
  [forall u in S, [forall v in S, ~~ (u -- v)]].

(** ** Statement *)

Definition OPG_digraph_stable_set_meets_longest_paths : Prop :=
  forall D : diGraph, irreflexive (@edge_rel D) ->
    exists S : {set D}, arc_free S /\
      forall (x : D) (s : seq D), dipath x s -> size s = longest_dipath_length D ->
        exists2 v : D, v \in S & v \in x :: s.
