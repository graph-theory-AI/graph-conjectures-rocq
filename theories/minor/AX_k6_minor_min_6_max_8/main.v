(** * K_6 minors in graphs of minimum degree 6 and maximum degree 8

Chudnovsky, Scott, Seymour, Spirkl, "Bipartite graphs with no K_6 minor", arXiv:2204.10119,
informal conjecture stated after Conjecture 1.3 (2204.10119__01).

Conjecture: every nonempty graph with minimum degree at least 6 and maximum degree at most 8 has a
K_6 minor.

Encoding.  Graphs are finite and simple. *)

From GraphTheory Require Import digraph sgraph minor.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

(** The maximum degree of [G] (0 if [G] is empty). *)
Definition Delta (G : sgraph) : nat := \max_(x : G) #|N(x)|.

(** Every vertex has degree at least [d] (true if [G] is empty). *)
Definition min_degree_ge (G : sgraph) (d : nat) : Prop := forall v : G, d <= #|N(v)|.

(** ** Statement *)

Definition AX_k6_minor_min_6_max_8 : Prop :=
  forall G : sgraph,
    0 < #|G| -> min_degree_ge G 6 -> Delta G <= 8 -> minor G 'K_6.
