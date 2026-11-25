(** * Jørgensen's conjecture

Jørgensen; Open Problem Garden, jorgensens_conjecture.

A graph is apex if it is planar after the deletion of some vertex.

Conjecture: every 6-connected graph without K_6 minor is apex.

Encoding.  Graphs are finite and simple.  Planarity is the absence of minors K_5 and K_3,3. *)

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

(** [G] is planar after the deletion of some vertex. *)
Definition apex (G : sgraph) : Prop := planar_after_deleting G 1.

(** ** Statement *)

Definition OPG_jorgensen_highly_connected_no_k6_minor_apex : Prop :=
  forall G : sgraph,
    6.-connected G -> ~ minor G 'K_6 -> apex G.
