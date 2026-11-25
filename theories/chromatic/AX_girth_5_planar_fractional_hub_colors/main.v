(** * Set colourings of triangle-free planar graphs with many colours at a vertex

Dvořák, Hu, "Fractional coloring of planar graphs of girth five", arXiv:1809.05439, remark after
Theorem 5 (1809.05439__00).

A set colouring of a graph assigns to each vertex a set of colours so that adjacent vertices receive
disjoint sets.  Theorem 5: for every triangle-free planar graph G and every vertex x, there is a set
colouring of G by subsets of {1,...,6} such that all vertices get at least two colours and x gets
three.

The authors suggest that it could be true that, for every triangle-free planar graph G and every
vertex x, there exists a set colouring of G by subsets of {1,...,9} such that all vertices get at
least three colours and x gets five.

Encoding.  Graphs are finite and simple.  Planarity is the absence of minors K_5 and K_3,3.  The
vertex x gets exactly five colours, which is equivalent to at least five. *)

From GraphTheory Require Import digraph sgraph minor.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

(** [G] has no triangle. *)
Definition triangle_free (G : sgraph) : Prop :=
  forall x y z : G, x -- y -> y -- z -> z -- x -> False.

(** ** Definitions copied from GraphLib/topological.v *)

(** [G] is planar: it has no minor [K_5] or [K_3,3]. *)
Definition planar (G : sgraph) : Prop :=
  ~ minor G 'K_5 /\ ~ minor G (KB 3 3).

(** ** Statement *)

Definition AX_girth_5_planar_fractional_hub_colors : Prop :=
  forall G : sgraph, planar G -> triangle_free G -> forall x : G,
    exists phi : G -> {set 'I_9},
      [/\ forall v : G, 3 <= #|phi v|, #|phi x| = 5
        & forall u v : G, u -- v -> [disjoint phi u & phi v]].
