(** * Linear forests and a matching in planar graphs of odd maximum degree

Bonamy, Czyżewska, Kowalik, Pilipczuk, "Partitioning edges of a planar graph into linear forests and
a matching", arXiv:2302.13312, Conjecture 2 (2302.13312__00).

A linear forest is a forest whose components are paths.

Conjecture 2: for every planar graph G of odd maximum degree Δ >= 7, the edges of G can be
partitioned into (Δ-1)/2 linear forests and one matching.

Encoding.  Graphs are finite and simple.  Planarity is defined by excluded minors (Wagner's
theorem).  The partition is a colouring of the edges with q + 1 colours, where q = (Δ-1)/2.  The
colouring is defined on all sets of vertices, but only its values on edges matter.  Its classes may
be empty, as a subset of a linear forest or of a matching is of the same kind. *)

From GraphTheory Require Import digraph sgraph minor.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

(** The maximum degree of [G] (0 if [G] is empty). *)
Definition Delta (G : sgraph) : nat := \max_(x : G) #|N(x)|.

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

(** [G] is a disjoint union of paths. *)
Definition linear_forest (G : sgraph) : Prop := is_forest [set: G] /\ Delta G <= 2.

(** ** Definitions copied from GraphLib/chromatic.v *)

(** The spanning subgraph formed by the edges with colour in [p]. *)
Definition edge_color_class (G : sgraph) (C : eqType) (col : {set G} -> C) (p : pred C) : sgraph :=
  del_edge_set [set e : {set G} | ~~ p (col e)].

(** ** Definitions copied from GraphLib/topological.v *)

(** [G] is planar: it has no minor [K_5] or [K_3,3]. *)
Definition planar (G : sgraph) : Prop :=
  ~ minor G 'K_5 /\ ~ minor G (KB 3 3).

(** ** Definitions specific to the conjecture *)

(** The edges of colour [i] form a matching. *)
Definition matching_colour
    (G : sgraph) (q : nat) (col : {set G} -> 'I_q) (i : 'I_q) : Prop :=
  forall v : G, #|[set e in E(G) | (col e == i) && (v \in e)]| <= 1.

(** Each of the [q] first colours forms a linear forest, the last one forms a matching. *)
Definition linear_forests_and_matching
    (G : sgraph) (q : nat) (col : {set G} -> 'I_q.+1) : Prop :=
  (forall i : 'I_q, linear_forest (edge_color_class col (pred1 (widen_ord (leqnSn q) i)))) /\
  matching_colour col ord_max.

(** ** Statement *)

Definition AX_planar_odd_degree_linear_forests_matching : Prop :=
  forall G : sgraph,
    planar G ->
    odd (Delta G) ->
    7 <= Delta G ->
    let q := (Delta G - 1) %/ 2 in
    exists col : {set G} -> 'I_q.+1, linear_forests_and_matching col.
