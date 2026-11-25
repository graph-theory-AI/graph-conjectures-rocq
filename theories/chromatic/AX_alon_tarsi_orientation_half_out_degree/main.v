(** * Alon-Tarsi orientations of spanning subgraphs with large outdegrees

Bradshaw, Chen, Ma, Mohar, Wu, "List-avoiding orientations", arXiv:2209.09107, Question 6.1
(2209.09107__00).

For an orientation D of a graph, a spanning subgraph is Eulerian if every vertex has equal indegree
and outdegree in it.  D is an Alon-Tarsi orientation if the number of Eulerian subgraphs with an
even number of edges differs from the number of those with an odd number of edges.

Question 6.1: does every graph G have a spanning subgraph with an Alon-Tarsi orientation in which
each vertex v has outdegree at least (deg_G(v) - 1) / 2?

The proposition states the positive answer.

Encoding.  Graphs are finite and simple.  The orientation of the spanning subgraph is a set of pairs
of vertices that are edges of G, without opposite pairs. *)

From GraphTheory Require Import digraph sgraph.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/digraph.v *)

(** Out-degree. *)
Definition outdeg (D : diGraph) (v : D) : nat := #|N(v)|.

(** In-degree. *)
Definition indeg (D : diGraph) (v : D) : nat := #|[set u | u -- v]|.

(** Each vertex has as many in-neighbours as out-neighbours (such a digraph is also called
    eulerian, connected or not). *)
Definition balanced_digraph (D : diGraph) : bool := [forall v : D, indeg v == outdeg v].

(** The digraph on [T] with arc set [A]. *)
Definition digraph_of_arcs (T : finType) (A : {set T * T}) : diGraph :=
  DiGraph (fun x y : T => (x, y) \in A).

(** ** Definitions copied from GraphLib/chromatic.v *)

(** The Eulerian subsets of the arc set [A]: indegrees and outdegrees are equal. *)
Definition eulerian_subsets (V : finType) (A : {set V * V}) : {set {set V * V}} :=
  [set B : {set V * V} | (B \subset A) && balanced_digraph (digraph_of_arcs B)].

(** [A] is an Alon-Tarsi orientation: it has not the same numbers of Eulerian subsets with an
    even number of arcs and with an odd number of arcs. *)
Definition alon_tarsi (V : finType) (A : {set V * V}) : bool :=
  #|[set B in eulerian_subsets A | ~~ odd #|B|]| != #|[set B in eulerian_subsets A | odd #|B|]|.

(** ** Statement *)

Definition AX_alon_tarsi_orientation_half_out_degree : Prop :=
  forall G : sgraph, exists A : {set G * G},
    [/\ forall x y : G, (x, y) \in A -> x -- y /\ (y, x) \notin A,
        alon_tarsi A
      & forall v : G, #|N(v)| <= (2 * outdeg (D := digraph_of_arcs A) v).+1].
