(** * Forcing a K_6 minor

Barát, Joret, Wood, "Disproof of the List Hadwiger Conjecture", Electron. J. Combin. 18 (2011),
P232; the second conjecture was first asked by Kawarabayashi and Toft (2005).  Open Problem Garden,
forcing_a_k_6_minor.

Conjecture: every graph with minimum degree at least 7 contains a K_6 minor.

Conjecture: every 7-connected graph contains a K_6 minor.

The proposition states both.

Encoding.  Graphs are finite, simple and nonempty. *)

From GraphTheory Require Import digraph sgraph connectivity minor.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

(** Every vertex has degree at least [d] (true if [G] is empty). *)
Definition min_degree_ge (G : sgraph) (d : nat) : Prop := forall v : G, d <= #|N(v)|.

(** ** Statement *)

Definition OPG_min_degree_7_forces_k6_minor : Prop :=
  (forall G : sgraph, 0 < #|G| ->
      min_degree_ge G 7 -> minor G 'K_6)
  /\
  (forall G : sgraph, 0 < #|G| ->
      7.-connected G -> minor G 'K_6).
