(** * 4-regular 4-chromatic graphs of high girth

Grünbaum; Open Problem Garden, high_girth_low_degree_4_chromatic_graphs.

Problem: do there exist 4-regular 4-chromatic graphs of arbitrarily high girth?

The proposition states the positive answer: for every g, some 4-regular graph has chromatic
number 4 and girth at least g.

Encoding.  Graphs are finite and simple. *)

From GraphTheory Require Import digraph sgraph coloring.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

(** Every vertex has degree [d]. *)
Definition regular (G : sgraph) (d : nat) : Prop := forall v : G, #|N(v)| = d.

Section Cycles.
Variables (T : eqType) (r : rel T).
Implicit Types c : seq T.

(** [c] is a cycle (without repetition, of length at least 3) of the relation [r]. *)
Definition seq_cycle c : bool := ucycleb r c && (2 < size c).

End Cycles.

(** The girth of [G] is at least [g] (true if [G] is a forest). *)
Definition girth_ge (G : sgraph) (g : nat) : Prop :=
  forall c : seq G, seq_cycle (--) c -> g <= size c.

(** ** Statement *)

Definition OPG_4_regular_4_chromatic_high_girth : Prop :=
  forall g : nat, exists G : sgraph,
    [/\ regular G 4, χ([set: G]) = 4 & girth_ge G g].
