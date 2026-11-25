(** * Bollobás-Eldridge-Catlin conjecture

Bollobás, Eldridge, "Maximal matchings in graphs with given maximal and minimal degrees", Congr.
Numer. XV (1976); Catlin, "Embedding subgraphs and coloring graphs under extremal degree
conditions", PhD thesis, Ohio State University, 1976; Open Problem Garden,
the_bollobas_eldridge_catlin_conjecture_on_graph_packing.

Two graphs with n vertices pack if they have edge-disjoint copies on the same n vertices.  The
maximum degree of G is denoted by Δ(G).

Conjecture: if G_1 and G_2 are graphs with n vertices and (Δ(G_1) + 1)(Δ(G_2) + 1) < n + 1, then G_1
and G_2 pack.

Encoding.  Graphs are finite and simple.  The inequality is strict, as in the Open Problem
Garden; the conjecture is usually stated with <= n + 1, which is stronger. *)

From GraphTheory Require Import digraph sgraph.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

(** The maximum degree of [G] (0 if [G] is empty). *)
Definition Delta (G : sgraph) : nat := \max_(x : G) #|N(x)|.

(** ** Definitions copied from GraphLib/packing.v *)

(** [G1] and [G2] pack: they have edge-disjoint copies on the same vertices. *)
Definition packs (G1 G2 : sgraph) : Prop :=
  exists f : G1 -> G2,
    bijective f /\ forall x y : G1, x -- y -> ~~ (f x -- f y).

(** ** Statement *)

Definition OPG_bollobas_eldridge_catlin_max_degree_packing : Prop :=
  forall (n : nat) (G1 G2 : sgraph),
    #|G1| = n -> #|G2| = n ->
    (Delta G1 + 1) * (Delta G2 + 1) < n + 1 ->
    packs G1 G2.
