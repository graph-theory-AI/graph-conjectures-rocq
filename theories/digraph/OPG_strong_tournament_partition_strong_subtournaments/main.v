(** * Partition of a tournament into strongly connected subtournaments

Thomassen; Reid, "Three problems on tournaments", Ann. New York Acad. Sci. 576 (1989); Open
Problem Garden, partitionning_a_tournament_into_k_strongly_connected_subtournaments.

A tournament is an orientation of a complete graph.  A digraph is k-strong if it has at least
k+1 vertices and remains strongly connected when fewer than k vertices are deleted.

Question: let k_1, ..., k_p be positive integers.  Does there exist an integer g(k_1, ..., k_p)
such that every g(k_1, ..., k_p)-strong tournament T admits a partition (V_1, ..., V_p) of its
vertex set such that the subtournament induced by V_i is non-trivial and k_i-strong for all
1 <= i <= p?

The proposition states the positive answer.

Encoding.  Tournaments are digraphs of GraphTheory ([diGraph]: a finite type of vertices with a
boolean relation [--]) satisfying the predicate [tournament].  The numbers k_i are given by a list
[ks] with p >= 1 elements, and the sets V_i by a list [part] of the same length.  A non-trivial
tournament has at least two vertices (a k_i-strong one has at least k_i + 1). *)

From GraphTheory Require Import digraph.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/digraph.v *)

(** [D] is a tournament: it has no loop, and exactly one arc between any two distinct vertices. *)
Definition tournament (D : diGraph) : Prop :=
  irreflexive (@edge_rel D) /\ forall x y : D, (x != y) = (x -- y) (+) (y -- x).

(** [D] is strongly connected. *)
Definition strongly_connected (D : diGraph) : bool :=
  [forall x : D, forall y : D, connect (--) x y].

(** [D] is [k]-strong: it has more than [k] vertices, and it remains strongly connected when
    fewer than [k] vertices are deleted. *)
Definition kstrong (D : diGraph) (k : nat) : bool :=
  (k < #|D|) && [forall S : {set D}, (#|S| < k) ==> strongly_connected (induced (~: S))].

(** ** Definitions specific to the conjecture *)

(** Each vertex is in exactly one set of the list [part]. *)
Definition set_partition (D : diGraph) (part : seq {set D}) : bool :=
  [forall v : D, count (fun A : {set D} => v \in A) part == 1].

(** ** Statement *)

Definition OPG_strong_tournament_partition_strong_subtournaments : Prop :=
  exists g : seq nat -> nat,
    forall ks : seq nat, 0 < size ks -> all (fun k => 0 < k) ks ->
      forall T : diGraph, tournament T -> kstrong T (g ks) ->
        exists part : seq {set T},
          [/\ size part = size ks, set_partition part &
              forall i : 'I_(size ks),
                1 < #|nth set0 part i| /\ kstrong (induced (nth set0 part i)) (nth 0 ks i)].
