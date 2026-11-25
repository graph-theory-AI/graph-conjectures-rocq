(** * Double-critical graphs

Erdős, Lovász, Problem 2 in "Theory of Graphs" (Proc. Colloq. Tihany, 1966), Academic Press, 1968;
Open Problem Garden, double_critical_graph_conjecture.

A connected simple graph G is double-critical if removing any pair of adjacent vertices decreases
its chromatic number by 2.

Conjecture: K_n is the only n-chromatic double-critical graph.

Encoding.  Graphs are finite, simple and nonempty.  Connectivity is a separate hypothesis. *)

From GraphTheory Require Import bij digraph sgraph coloring.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/chromatic.v *)

(** [G] is double-critical: deleting both ends of any edge decreases the chromatic number
    by 2. *)
Definition double_critical (G : sgraph) : Prop :=
  forall x y : G, x -- y -> χ([set: G] :\: [set x; y]) + 2 = χ([set: G]).

(** ** Statement *)

Definition OPG_double_critical_graphs_are_complete : Prop :=
  forall (G : sgraph) (n : nat),
    0 < #|G| -> connected [set: G] -> double_critical G ->
    χ([set: G]) = n -> inhabited (G ≃ 'K_n).
