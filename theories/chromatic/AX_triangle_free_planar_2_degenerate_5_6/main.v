(** * Induced 2-degenerate subgraphs of triangle-free planar graphs

Dvořák, Kelly, "Induced 2-degenerate Subgraphs of Triangle-free Planar Graphs", arXiv:1709.04036,
remark of the introduction (1709.04036__01).

A graph is k-degenerate if each of its nonempty subgraphs has a vertex of degree at most k.

The authors believe that their argument, which gives 4/5, can be strengthened to prove that every
triangle-free planar graph contains an induced 2-degenerate subgraph on at least 5/6 of its
vertices.  The proposition states this existence.

Encoding.  Graphs are finite and simple.  Planarity is defined by excluded minors (Wagner's
theorem). *)

From GraphTheory Require Import digraph sgraph minor.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

(** The subgraph induced by [W] is [k]-degenerate: each nonempty subset [S] of [W] has a
    vertex with at most [k] neighbours in [S]. *)
Definition degenerate_on (G : sgraph) (W : {set G}) (k : nat) : Prop :=
  forall S : {set G}, S \subset W -> S != set0 -> exists x, (x \in S) /\ #|N(x) :&: S| <= k.
Arguments degenerate_on {G} W k.

(** [G] is [k]-degenerate. *)
Definition degenerate (G : sgraph) (k : nat) : Prop :=
  degenerate_on [set: G] k.

(** [G] has no triangle. *)
Definition triangle_free (G : sgraph) : Prop :=
  forall x y z : G, x -- y -> y -- z -> z -- x -> False.

(** ** Definitions copied from GraphLib/topological.v *)

(** [G] is planar: it has no minor [K_5] or [K_3,3]. *)
Definition planar (G : sgraph) : Prop :=
  ~ minor G 'K_5 /\ ~ minor G (KB 3 3).

(** ** Statement *)

Definition AX_triangle_free_planar_2_degenerate_5_6 : Prop :=
  forall G : sgraph,
    planar G ->
    triangle_free G ->
    exists S : {set G}, 5 * #|G| <= 6 * #|S| /\ degenerate (induced S) 2.
