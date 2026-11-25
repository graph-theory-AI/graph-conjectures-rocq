(** * Vertex-critical graphs whose chromatic number resists the deletion of r edges

Martinsson, Steiner, "Vertex-critical graphs far from edge-criticality", arXiv:2310.12891
(2310.12891__00); a problem of Erdős.

A k-chromatic graph G is vertex-critical if χ(G - v) = k - 1 for every vertex v.

Problem: for every fixed k >= 4 and arbitrarily large r, does there exist a k-chromatic
vertex-critical graph G such that χ(G - R) = k for every set R of edges of G with |R| <= r?

The proposition states the positive answer.

Encoding.  Graphs are finite and simple.  The proposition is about all r: a graph that is suitable
for some r is also suitable for the smaller ones. *)

From GraphTheory Require Import digraph sgraph coloring.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

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

(** The chromatic number of [G] is [k] after the deletion of any set of at most [r] edges. *)
Definition edge_robust (G : sgraph) (k r : nat) : Prop :=
  forall R : {set {set G}}, R \subset E(G) -> #|R| <= r -> χ([set: del_edge_set R]) = k.

(** ** Statement *)

Definition AX_vertex_critical_edge_robust_fixed_k : Prop :=
  forall k r : nat, 4 <= k ->
    exists G : sgraph,
      [/\ χ([set: G]) = k, vertex_critical G & edge_robust G k r].
