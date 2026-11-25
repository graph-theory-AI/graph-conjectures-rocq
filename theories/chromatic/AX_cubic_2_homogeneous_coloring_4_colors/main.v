(** * 2-homogeneous colourings of cubic graphs with four colours

Barát, Dvořák, Haxell, Kardoš, Lužar, Onderko, Rajník, Soták, Ulyanov, "Open problems of the 33rd
Workshop on Cycles and Colourings", arXiv:2511.02892, Problem 5.1 (2511.02892__04).

A k-homogeneous colouring is a proper vertex colouring in which exactly k colours appear in the open
neighbourhood of every vertex.

Conjecture: if a cubic graph admits a 2-homogeneous colouring, then 4 colours are always sufficient.

Encoding.  Graphs are finite and simple. *)

From GraphTheory Require Import digraph sgraph coloring.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

(** Every vertex has degree [d]. *)
Definition regular (G : sgraph) (d : nat) : Prop := forall v : G, #|N(v)| = d.

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

(** ** Statement *)

Definition AX_cubic_2_homogeneous_coloring_4_colors : Prop :=
  forall G : sgraph,
    regular G 3 ->
    homogeneous_colorable G 2 ->
    exists col : G -> 'I_4, homogeneous_coloring col 2.
