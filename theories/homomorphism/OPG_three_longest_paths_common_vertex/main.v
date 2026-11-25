(** * Three longest paths in a connected graph

Gallai, Problem 6, "Theory of Graphs" (Proc. Colloq., Tihany, 1966), Academic Press, 1968; Open
Problem Garden, do_any_three_longest_paths_in_a_connected_graph_have_a_vertex_in_common.

A longest path of a graph is a path of maximum length.

Problem: do any three longest paths in a connected graph have a vertex in common?

The proposition states the positive answer.

Encoding.  Graphs are finite and simple.  Paths are nonempty sequences of vertices.  The three paths
may be equal, which is harmless since two longest paths in a connected graph always have a common
vertex. *)

From GraphTheory Require Import digraph sgraph.
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

(** [p] is a longest path. *)
Definition seq_longest_path p : Prop :=
  seq_simple_path p /\ forall q : seq G, seq_simple_path q -> size q <= size p.

End Paths.

(** ** Statement *)

Definition OPG_three_longest_paths_common_vertex : Prop :=
  forall (G : sgraph) (p q r : seq G),
    connected [set: G] -> seq_longest_path p -> seq_longest_path q -> seq_longest_path r ->
    exists v : G, [/\ v \in p, v \in q & v \in r].
