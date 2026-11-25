(** * The seagull problem

Seymour; Open Problem Garden, seagull_problem.

Conjecture: every graph on n vertices with no independent set of size 3 has a complete graph on at
least n/2 vertices as a minor.

Encoding.  Graphs are finite, simple and nonempty.  "No independent set of size 3" is α(G) <= 2, and
the minor is the complete graph on ⌈n/2⌉ vertices, which is equivalent. *)

From GraphTheory Require Import digraph sgraph coloring minor.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

(** The ceiling of [a / b] (0 if [b = 0]). *)
Definition ceil_div (a b : nat) : nat := (a + b - 1) %/ b.

(** ** Statement *)

Definition OPG_seagull_independence_2_clique_minor_half_n : Prop :=
  forall G : sgraph, 0 < #|G| ->
    α(G) <= 2 -> minor G 'K_(ceil_div #|G| 2).
