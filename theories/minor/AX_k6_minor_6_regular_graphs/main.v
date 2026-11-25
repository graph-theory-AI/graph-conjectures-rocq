(** * K_6 minors in 6-regular graphs

Chudnovsky, Scott, Seymour, Spirkl, "Bipartite graphs with no K_6 minor", arXiv:2204.10119,
Conjecture 1.3 (2204.10119__00).

Conjecture 1.3: every nonempty 6-regular graph has a K_6 minor.

Encoding.  Graphs are finite and simple. *)

From GraphTheory Require Import digraph sgraph minor.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

(** Every vertex has degree [d]. *)
Definition regular (G : sgraph) (d : nat) : Prop := forall v : G, #|N(v)| = d.

(** ** Statement *)

Definition AX_k6_minor_6_regular_graphs : Prop :=
  forall G : sgraph, 0 < #|G| -> regular G 6 -> minor G 'K_6.
