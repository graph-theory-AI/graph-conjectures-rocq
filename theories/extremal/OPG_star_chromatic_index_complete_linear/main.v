(** * Star chromatic index of complete graphs

Dvořák, Mohar, Šámal, "Star chromatic index", arXiv:1011.3376; Open Problem Garden,
star_chromatic_index_of_complete_graphs.

A star edge colouring is a proper edge colouring such that no path and no cycle with four edges has
only two colours.  The star chromatic index is the minimum number of colours of a star edge
colouring.

Question: is the star chromatic index of the complete graph K_n linear in n, that is, O(n)?  The
proposition states the positive answer.

Encoding.  "The star chromatic index is k" is a relation between a graph and k (it exists for all
graphs). *)

From GraphTheory Require Import preliminaries digraph sgraph.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

(** [P n] holds for every sufficiently large [n]. *)
Definition eventually (P : nat -> Prop) : Prop :=
  exists N : nat, forall n : nat, N <= n -> P n.

(** ** Definitions copied from GraphLib/chromatic.v *)

(** [col] is a proper edge colouring. *)
Definition proper_edge_coloring (G : sgraph) (C : eqType) (col : {set G} -> C) : Prop :=
  forall x y z : G, x -- y -> x -- z -> y != z -> col [set x; y] != col [set x; z].

(** [col] is a star edge colouring: it is proper, and no path or cycle with four edges has only
    two colours. *)
Definition star_edge_coloring (G : sgraph) (C : finType) (col : {set G} -> C) : Prop :=
  [/\ proper_edge_coloring col,
      (forall a b c d e : G,
         uniq [:: a; b; c; d; e] -> a -- b -> b -- c -> c -- d -> d -- e ->
         2 < #|[set col [set a; b]; col [set b; c]; col [set c; d]; col [set d; e]]|)
    & (forall a b c d : G,
         uniq [:: a; b; c; d] -> a -- b -> b -- c -> c -- d -> d -- a ->
         2 < #|[set col [set a; b]; col [set b; c]; col [set c; d]; col [set d; a]]|)].

(** [G] is star [k]-edge-colourable ([0 < k] is meant). *)
Definition star_edge_colorable (G : sgraph) (k : nat) : Prop :=
  exists col : {set G} -> 'I_k, star_edge_coloring col.

(** The star chromatic index of [G] is [k]. *)
Definition star_chromatic_index (G : sgraph) (k : nat) : Prop :=
  star_edge_colorable G k /\
  (forall k', star_edge_colorable G k' -> (k <= k')%N).

(** ** Statement *)

Definition OPG_star_chromatic_index_complete_linear : Prop :=
  exists c : nat,
    eventually (fun n => forall k : nat, star_chromatic_index 'K_n k -> k <= c * n).
