(** * Reducing the matching number of r-partite hypergraphs by deleting vertices

Clow, Haxell, Mohar, "A counterexample to a conjecture of Lovász", arXiv:2505.05339, Conjecture 4.3
(2505.05339__02).

A hypergraph is r-partite and r-uniform if its vertices can be partitioned into r parts such that
every edge has exactly one vertex in each part.  The matching number ν is the maximum number of
pairwise disjoint edges.  Deleting a vertex also deletes the edges that contain it.

Conjecture 4.3: for every r-partite r-uniform hypergraph H, there is some k with 1 <= k <= r - 1
such that H has k(r - 1) vertices whose deletion reduces the matching number by at least k.

Encoding.  r >= 2 and H has at least one edge: otherwise there is no such k, or ν = 0.  The
remaining edges after deletion of a set X of vertices are the edges contained in the complement of
X.  If ν' is their matching number, the inequality ν' <= ν - k is written ν' + k <= ν. *)

From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/hypergraph.v *)

Section Hypergraph.
Variable T : finType.
Implicit Types (E M : {set {set T}}) (e S : {set T}).

(** [E] is [k]-partite and [k]-uniform for the partition given by [part]: every edge has exactly
    one vertex in each part. *)
Definition hg_partite_uniform (k : nat) (part : T -> 'I_k) E : Prop :=
  forall e, e \in E -> forall j : 'I_k, #|[set v in e | part v == j]| = 1.

(** The edges contained in [S]. *)
Definition hg_restrict E S : {set {set T}} := [set e in E | e \subset S].

(** [M] is a matching: a set of pairwise disjoint edges. *)
Definition hg_matching M E : Prop :=
  M \subset E /\ trivIset M.

(** The matching number (maximum number of edges of a matching) of [E] is [nu]. *)
Definition hg_matching_number E (nu : nat) : Prop :=
  (exists M : {set {set T}}, hg_matching M E /\ #|M| = nu) /\
  (forall M : {set {set T}}, hg_matching M E -> #|M| <= nu).

End Hypergraph.

(** ** Statement *)

Definition AX_r_partite_hypergraph_matching_drop_deletion : Prop :=
  forall (r : nat) (T : finType) (part : T -> 'I_r) (E : {set {set T}}) (nu : nat),
    1 < r ->
    E != set0 ->
    hg_partite_uniform part E ->
    hg_matching_number E nu ->
    exists (k : nat) (X : {set T}),
      [/\ 1 <= k, k <= r - 1, #|X| = k * (r - 1) &
        exists nu' : nat, hg_matching_number (hg_restrict E (~: X)) nu' /\ nu' + k <= nu].
