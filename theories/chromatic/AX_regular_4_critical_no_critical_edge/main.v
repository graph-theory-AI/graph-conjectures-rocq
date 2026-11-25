(** * 6-regular 4-vertex-critical graphs without critical edge

Skottová, Steiner, "Critical edge sets in vertex-critical graphs", arXiv:2508.08703, Problem 5.2
(2508.08703__00).

A vertex, edge or set of edges of a graph G is critical if its removal decreases the chromatic
number of G.  A (k,r)-graph is a graph of chromatic number k in which every vertex is critical and
no set of at most r edges is critical.

Problem 5.2: does there exist a 6-regular (4,1)-graph?

The proposition states the positive answer.

Encoding.  Graphs are finite and simple. *)

From GraphTheory Require Import digraph sgraph coloring.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

(** Every vertex has degree [d]. *)
Definition regular (G : sgraph) (d : nat) : Prop := forall v : G, #|N(v)| = d.

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

(** ** Definitions copied from GraphLib/chromatic.v *)

(** [G] is vertex-critical: deleting any vertex decreases the chromatic number. *)
Definition vertex_critical (G : sgraph) : Prop := forall v : G, χ([set: G] :\ v) < χ([set: G]).

(** ** Definitions specific to the conjecture *)

(** The chromatic number of [G] is [k] after the deletion of any edge (with [χ(G) = k], no edge
    of [G] is critical). *)
Definition no_critical_edge (G : sgraph) (k : nat) : Prop :=
  forall e : {set G}, e \in E(G) -> χ([set: del_edge_set [set e]]) = k.

(** [G] is a (4,1)-graph. *)
Definition four_one_graph (G : sgraph) : Prop :=
  [/\ χ([set: G]) = 4, vertex_critical G & no_critical_edge G 4].

(** ** Statement *)

Definition AX_regular_4_critical_no_critical_edge : Prop :=
  exists G : sgraph, regular G 6 /\ four_one_graph G.
