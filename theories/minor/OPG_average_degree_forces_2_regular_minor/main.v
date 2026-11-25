(** * Average degree and 2-regular minors

Reed, Wood, "Forcing a sparse minor", arXiv:1402.0272; Open Problem Garden,
forcing_a_2_regular_minor.

Conjecture: every graph with average degree at least (4/3) t - 2 contains every 2-regular graph on
t vertices as a minor.

Encoding.  Graphs are finite and simple.  G is nonempty, and t >= 3, as a 2-regular graph has at
least three vertices.  The bound is (4t - 6) / 3, and the average degree is compared with it without
division. *)

From GraphTheory Require Import digraph sgraph minor.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

(** Every vertex has degree [d]. *)
Definition regular (G : sgraph) (d : nat) : Prop := forall v : G, #|N(v)| = d.

(** The average degree of [G] is at least [a / b]. *)
Definition average_degree_ge (G : sgraph) (a b : nat) : Prop :=
  a * #|G| <= b * (\sum_(v in G) #|N(v)|).

(** ** Statement *)

Definition OPG_average_degree_forces_2_regular_minor : Prop :=
  forall (t : nat) (G H : sgraph),
    3 <= t ->
    0 < #|G| ->
    average_degree_ge G (4 * t - 6) 3 ->
    regular H 2 -> #|H| = t ->
    minor G H.
