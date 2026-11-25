(** * The weak pentagon problem

DeVos, Šámal, "High girth cubic graphs map to the Clebsch graph", arXiv:math/0602580; Open Problem
Garden, weak_pentagon_problem.

Conjecture: if G is a cubic graph without triangle, then it is possible to colour the edges of G by
five colours, so that the complement of every colour class is a bipartite graph.

Encoding.  Graphs are finite and simple.  A colouring of the edges gives a colour to each set of
vertices, and only the colours of the edges matter.  The complement of a colour class is the
spanning subgraph formed by the edges that are not in this class. *)

From GraphTheory Require Import digraph sgraph connectivity.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

(** Every vertex has degree [d]. *)
Definition regular (G : sgraph) (d : nat) : Prop := forall v : G, #|N(v)| = d.

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

(** ** Definitions copied from GraphLib/chromatic.v *)

(** The spanning subgraph formed by the edges with colour in [p]. *)
Definition edge_color_class (G : sgraph) (C : eqType) (col : {set G} -> C) (p : pred C) : sgraph :=
  del_edge_set [set e : {set G} | ~~ p (col e)].

(** ** Statement *)

Definition OPG_pentagon_weak_cubic_5_edge_coloring : Prop :=
  forall G : sgraph, regular G 3 -> triangle_free G ->
    exists col : {set G} -> 'I_5, forall i : 'I_5, bipartite (edge_color_class col (predC1 i)).
