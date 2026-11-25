(** * Bridgeless cubic graphs without 2-homogeneous colouring

Barát, Dvořák, Haxell, Kardoš, Lužar, Onderko, Rajník, Soták, Ulyanov, "Open problems of the 33rd
Workshop on Cycles and Colourings", arXiv:2511.02892, Problem 5.2 (2511.02892__05).

A k-homogeneous colouring is a proper vertex colouring in which exactly k colours appear in the open
neighbourhood of every vertex.

Conjecture: there is a finite number of connected bridgeless cubic graphs that do not admit a
2-homogeneous colouring.

Encoding.  Graphs are finite and simple.  The finiteness is expressed by a bound on the number of
vertices of the exceptions, which is equivalent.  A connected graph is bridgeless if it remains
connected after the deletion of any edge. *)

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

(** [col] is a proper colouring of [G]. *)
Definition proper_coloring (G : sgraph) (C : finType) (col : G -> C) : bool :=
  coloring (preim_partition col [set: G]) [set: G].

(** The colours of the neighbours of [v]. *)
Definition neighbor_colors (G : sgraph) (C : finType) (col : G -> C) (v : G) : {set C} :=
  [set c : C | [exists u : G, (u -- v) && (col u == c)]].

(** [col] is a [k]-homogeneous colouring: it is proper, and the neighbours of each vertex have
    [k] colours. *)
Definition homogeneous_coloring (G : sgraph) (C : finType) (col : G -> C) (k : nat) : Prop :=
  proper_coloring col /\ forall v : G, #|neighbor_colors col v| = k.

(** [G] has a [k]-homogeneous colouring. *)
Definition homogeneous_colorable (G : sgraph) (k : nat) : Prop :=
  exists (C : finType) (col : G -> C), homogeneous_coloring col k.

(** ** Definitions specific to the conjecture *)

(** [G] remains connected after the deletion of any edge. *)
Definition bridgeless_connected (G : sgraph) : Prop :=
  forall e : {set G}, e \in E(G) -> connected [set: del_edge_set [set e]].

(** ** Statement *)

Definition AX_cubic_2_homogeneous_coloring_finite_exceptions : Prop :=
  exists N : nat,
    forall G : sgraph,
      connected [set: G] -> regular G 3 -> bridgeless_connected G -> N <= #|G| ->
      homogeneous_colorable G 2.
