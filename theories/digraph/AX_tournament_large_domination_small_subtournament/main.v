(** * Small subtournaments with large domination number

Harutyunyan, Le, Thomassé, Wu, "Coloring tournaments: from local to global", 2017,
arXiv:1702.01607, Problem 4 (1702.01607__01).

A set S of vertices of a tournament T is dominating if every vertex outside S has an in-neighbour
in S.  The dominating number of T is the minimum size of a dominating set.

Problem 4: for every integer k >= 1, there exist integers K and ℓ such that every tournament with
dominating number at least K contains a subtournament with ℓ vertices and dominating number at
least k.

Encoding.  Tournaments are digraphs of GraphTheory ([diGraph]: a finite type of vertices with a
boolean relation [--]) satisfying the predicate [tournament]. *)

From GraphTheory Require Import digraph.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/digraph.v *)

(** [D] is a tournament: it has no loop, and exactly one arc between any two distinct vertices. *)
Definition tournament (D : diGraph) : Prop :=
  irreflexive (@edge_rel D) /\ forall x y : D, (x != y) = (x -- y) (+) (y -- x).

(** [X] dominates [D]: each vertex is in [X] or has an in-neighbour in [X]. *)
Definition out_dominating (D : diGraph) (X : {set D}) : bool :=
  [forall v : D, v \in NS[X]].

(** Domination number. *)
Definition out_domination_number (D : diGraph) : nat :=
  #|[arg min_(X < [set: D] | out_dominating X) #|X|]|.

(** ** Statement *)

Definition AX_tournament_large_domination_small_subtournament : Prop :=
  forall k : nat, 0 < k ->
    exists K ell : nat, forall T : diGraph, tournament T -> K <= out_domination_number T ->
      exists A : {set T}, #|A| = ell /\ k <= out_domination_number (induced A).
