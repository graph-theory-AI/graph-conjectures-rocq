(** * Odd-cycle transversal in triangle-free graphs

Erdős, Faudree, Pach, Spencer, "How to make a graph bipartite", J. Combin. Theory Ser. B 45 (1988),
86-98; Open Problem Garden, odd_cycle_transversal_in_triangle_free_graphs.

Conjecture: if G is a simple triangle-free graph with n vertices, then there is a set of at most
n²/25 edges whose deletion destroys every odd cycle.

Encoding.  Graphs are finite.  The deletion of a set of edges destroys every odd cycle if the
remaining graph is bipartite. *)

From GraphTheory Require Import digraph sgraph connectivity.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

(** [G] has no triangle. *)
Definition triangle_free (G : sgraph) : Prop :=
  forall x y z : G, x -- y -> y -- z -> z -- x -> False.

Section DelEdgeSet.
Variables (G : sgraph) (F : {set {set G}}).

(** The edges of [G] that are not in [F]. *)
Definition del_edge_set_rel : rel G := [rel x y : G | (x -- y) && ([set x; y] \notin F)].

Lemma del_edge_set_sym : symmetric del_edge_set_rel.
Proof. by move=> x y; rewrite /del_edge_set_rel /= sg_sym setUC. Qed.

Lemma del_edge_set_irrefl : irreflexive del_edge_set_rel.
Proof. by move=> x; rewrite /del_edge_set_rel /= sg_irrefl. Qed.

(** [G] without the edges of [F]. *)
Definition del_edge_set : sgraph := SGraph del_edge_set_sym del_edge_set_irrefl.

End DelEdgeSet.

(** [G] is bipartite: it has a bipartition (a set [A] such that each edge has exactly one end in
    [A]). *)
Definition bipartite (G : diGraph) : Prop := exists A : {set G}, bipartition A.

(** ** Statement *)

Definition OPG_triangle_free_odd_cycle_edge_transversal : Prop :=
  forall G : sgraph,
    triangle_free G ->
    exists S : {set {set G}},
      [/\ S \subset E(G), #|S| <= #|G| ^ 2 %/ 25 & bipartite (del_edge_set S)].
