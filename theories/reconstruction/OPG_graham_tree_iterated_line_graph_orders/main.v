(** * Graham's conjecture on tree reconstruction

Graham; Godsil and Royle, Algebraic graph theory (2001), page 18; Open Problem Garden,
grahams_conjecture_on_tree_reconstruction.

The line graph L(G) of a graph G has the edges of G as vertices, two of them being adjacent if
they are distinct and have a common end.

Question: given that G is a tree, can we determine it from the integer sequence |V(G)|, |V(L(G))|,
|V(L(L(G)))|, ...?  The answer stated is yes: two trees with the same sequence are isomorphic.

Encoding.  Graphs are finite and simple.  The i-th term of the sequence is the number of vertices
of the i-th iterate of L, from i = 0.  A tree may have no vertex, which does not matter since i = 0
gives the number of vertices. *)

From GraphTheory Require Import digraph sgraph.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

Section SimpleLineGraph.
Variable G : sgraph.

(** The edges of [G]. *)
Definition simple_line_vertex : Type := {e : {set G} | e \in E(G)}.

(** Distinct edges with a common end. *)
Definition simple_line_rel : rel simple_line_vertex :=
  fun e f => (val e != val f) && (val e :&: val f != set0).

Lemma simple_line_sym : symmetric simple_line_rel.
Proof. by move=> e f; rewrite /simple_line_rel eq_sym setIC. Qed.

Lemma simple_line_irrefl : irreflexive simple_line_rel.
Proof. by move=> e; rewrite /simple_line_rel eqxx. Qed.

(** The line graph of the simple graph [G]. *)
Definition simple_line_graph : sgraph := SGraph simple_line_sym simple_line_irrefl.

End SimpleLineGraph.

(** ** Statement *)

(** The positive answer. *)
Definition OPG_graham_tree_iterated_line_graph_orders : Prop :=
  forall T1 T2 : sgraph,
    is_tree [set: T1] -> is_tree [set: T2] ->
    (forall i : nat, #|iter i simple_line_graph T1| = #|iter i simple_line_graph T2|) ->
    inhabited (T1 ≃ T2).
