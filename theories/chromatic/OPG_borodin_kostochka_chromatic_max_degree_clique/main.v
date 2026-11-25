(** * The Borodin-Kostochka conjecture

Borodin, Kostochka, "On an upper bound of a graph's chromatic number, depending on the graph's
degree and density", J. Combin. Theory B 23 (1977); Open Problem Garden,
the_borodin_kostochka_conjecture.

Conjecture: every graph with maximum degree Δ >= 9 and clique number ω has chromatic number at
most max(Δ-1, ω).

Encoding.  Graphs are finite and simple. *)

From GraphTheory Require Import digraph sgraph coloring.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

(** The maximum degree of [G] (0 if [G] is empty). *)
Definition Delta (G : sgraph) : nat := \max_(x : G) #|N(x)|.

(** ** Statement *)

Definition OPG_borodin_kostochka_chromatic_max_degree_clique : Prop :=
  forall G : sgraph,
    9 <= Delta G -> χ([set: G]) <= maxn (Delta G - 1) ω([set: G]).
