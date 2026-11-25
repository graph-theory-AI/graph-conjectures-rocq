(** * Extension of 3-colourings of distant vertices in triangle-free planar graphs

Dvořák, Král', Thomas, "Three-coloring triangle-free graphs on surfaces V. Coloring planar graphs
with distant anomalies", arXiv:0911.0885, Conjecture 1.4 (0911.0885__00).

Conjecture 1.4: there exists an absolute constant d >= 2 with the following property.  Let G be a
plane triangle-free graph, let S be a set of vertices of G and let ψ : S -> {1,2,3} be an arbitrary
function.  If the distance between every two vertices of S is at least d, then ψ extends to a
3-colouring of G.

Encoding.  Graphs are finite and simple.  Planarity is the absence of minors K_5 and K_3,3 (the
embedding of the plane graph plays no role).  The function ψ is defined on all vertices, but only
its values on S are used. *)

From GraphTheory Require Import digraph sgraph coloring minor.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

(** [G] has no triangle. *)
Definition triangle_free (G : sgraph) : Prop :=
  forall x y z : G, x -- y -> y -- z -> z -- x -> False.

(** The vertices of [G] at distance at most [k] from [x]. *)
Definition ball (G : sgraph) (k : nat) (x : G) : {set G} := iter k (@closed_neigh_set G) [set x].

(** ** Definitions copied from GraphLib/chromatic.v *)

(** [col] is a proper colouring of [G]. *)
Definition proper_coloring (G : sgraph) (C : finType) (col : G -> C) : bool :=
  coloring (preim_partition col [set: G]) [set: G].

(** ** Definitions copied from GraphLib/topological.v *)

(** [G] is planar: it has no minor [K_5] or [K_3,3]. *)
Definition planar (G : sgraph) : Prop :=
  ~ minor G 'K_5 /\ ~ minor G (KB 3 3).

(** ** Definitions specific to the conjecture *)

(** Distinct vertices of [S] are at distance at least [d] ([0 < d] is meant). *)
Definition pairwise_distance_at_least (G : sgraph) (d : nat) (S : {set G}) : Prop :=
  forall x y : G, x \in S -> y \in S -> x != y -> y \notin ball d.-1 x.

(** ** Statement *)

Definition AX_plane_triangle_free_distant_precoloring_extension : Prop :=
  exists d : nat, 2 <= d /\
    forall (G : sgraph) (S : {set G}) (psi : G -> 'I_3),
      planar G -> triangle_free G -> pairwise_distance_at_least d S ->
      exists col : G -> 'I_3,
        proper_coloring col /\ forall v : G, v \in S -> col v = psi v.
