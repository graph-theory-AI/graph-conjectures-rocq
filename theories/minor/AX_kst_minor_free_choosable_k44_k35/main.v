(** * Choosability of K_{4,4}-minor-free and K_{3,5}-minor-free graphs

Steiner, "Disproof of a conjecture by Woodall", arXiv:2201.09115, Question 1 (2201.09115__00).

A graph is k-choosable if, whenever each vertex has a list of at least k colours, there is a
proper colouring where each vertex has a colour of its list.

Question 1: is every graph without K_{4,4} minor 7-choosable?  Is every graph without K_{3,5} minor
7-choosable?

Encoding.  Graphs are finite and simple.  The proposition states the positive answer to both
questions. *)

From GraphTheory Require Import digraph sgraph minor.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/chromatic.v *)

(** [f] is a proper colouring from the lists [L]. *)
Definition proper_list_coloring
    (G : sgraph) (C : finType) (L : G -> {set C}) (f : G -> C) : Prop :=
  (forall v : G, f v \in L v) /\
  (forall x y : G, x -- y -> f x != f y).

(** [G] has a proper colouring from the lists [L]. *)
Definition list_colorable (G : sgraph) (C : finType) (L : G -> {set C}) : Prop :=
  exists f : G -> C, proper_list_coloring L f.

(** [G] is [k]-choosable. *)
Definition choosable (G : sgraph) (k : nat) : Prop :=
  forall (C : finType) (L : G -> {set C}),
    (forall v : G, k <= #|L v|) -> list_colorable L.

(** ** Statement *)

Definition AX_kst_minor_free_choosable_k44_k35 : Prop :=
  (forall G : sgraph, ~ minor G (KB 4 4) -> choosable G 7) /\
  (forall G : sgraph, ~ minor G (KB 3 5) -> choosable G 7).
