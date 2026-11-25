(** * Triangle removal in C_5-free graphs

Conlon, Fox, Sudakov, Zhao, "The regularity method for graphs with few 4-cycles", arXiv:2004.10180,
optimality of Corollary 1.4 (2004.10180__00).

A graph is C_5-free if it has no cycle of length 5 as a subgraph (not necessarily induced).  Every
C_5-free graph with n vertices can be made triangle-free by deleting o(n^(3/2)) edges.

Question: is the exponent 3/2 best possible?

The proposition states that the answer is yes: for every δ > 0, it is not true that every C_5-free
graph with n vertices can be made triangle-free by deleting O(n^(3/2 - δ)) edges.

Encoding.  Graphs are finite and simple.  It suffices to consider δ = 1/q.  For all q >= 1, C and N,
there is a C_5-free graph with n >= N vertices such that every set F of edges whose deletion leaves
a triangle-free graph satisfies C n^(3q - 2) < |F|^(2q), that is, |F| > C' n^(3/2 - 1/q) with
C' = C^(1/(2q)). *)

From GraphTheory Require Import preliminaries digraph sgraph.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

Lemma sgraph_of_rel_sym (V : finType) (r : rel V) :
  symmetric (fun x y => (x != y) && sc r x y).
Proof. by move=> x y /=; rewrite eq_sym orbC. Qed.

Lemma sgraph_of_rel_irrefl (V : finType) (r : rel V) :
  irreflexive (fun x y => (x != y) && sc r x y).
Proof. by move=> x; rewrite eqxx. Qed.

(** The graph on [V] whose edges are given by [r], up to symmetry and loops. *)
Definition sgraph_of_rel (V : finType) (r : rel V) : sgraph :=
  SGraph (@sgraph_of_rel_sym V r) (@sgraph_of_rel_irrefl V r).

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

(** The cycle on [n] vertices ([3 <= n] is meant). *)
Definition cycle_graph (n : nat) : sgraph :=
  sgraph_of_rel (fun i j : 'I_n => (val i).+1 %% n == val j).

(** ** Statement *)

Definition AX_c5_free_triangle_removal_exponent : Prop :=
  forall q C N : nat, 1 <= q -> exists G : sgraph,
    [/\ N <= #|G|, ~ subgraph (cycle_graph 5) G &
      forall F : {set {set G}}, F \subset E(G) -> triangle_free (del_edge_set F) ->
        C * #|G| ^ (3 * q - 2) < #|F| ^ (2 * q)].
