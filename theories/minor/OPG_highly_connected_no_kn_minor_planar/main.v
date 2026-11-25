(** * Large highly connected graphs without K_n minor

Thomas; Open Problem Garden, high_connectivity_no_k_n.

Problem: is it true, for all n >= 0, that every sufficiently large n-connected graph without K_n
minor has a set of n - 5 vertices whose deletion results in a planar graph?

The proposition states the positive answer.

Encoding.  Graphs are finite and simple.  Planarity is the absence of minors K_5 and K_3,3.  The
subtraction n - 5 is truncated: for n <= 5, the graph itself has to be planar. *)

From GraphTheory Require Import digraph sgraph connectivity minor.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/topological.v *)

(** [G] is planar: it has no minor [K_5] or [K_3,3]. *)
Definition planar (G : sgraph) : Prop :=
  ~ minor G 'K_5 /\ ~ minor G (KB 3 3).

(** [G] is planar after the deletion of some set of [k] vertices. *)
Definition planar_after_deleting (G : sgraph) (k : nat) : Prop :=
  exists S : {set G}, #|S| = k /\ planar (induced (~: S)).

(** ** Statement *)

Definition OPG_highly_connected_no_kn_minor_planar : Prop :=
  forall n : nat,
    exists N : nat,
      forall G : sgraph,
        N <= #|G| -> n.-connected G -> ~ minor G 'K_n ->
        planar_after_deleting G (n - 5).
