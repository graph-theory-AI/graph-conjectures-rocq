(** * 3-choosability of planar graphs without cycles of lengths 4 to 7

Dvořák, Postle, "Correspondence coloring and its application to list-coloring planar graphs without
cycles of lengths 4 to 8", arXiv:1508.03437, open questions (1508.03437__00).

A graph is k-choosable if, whenever each vertex has a list of at least k colours, there is a proper
colouring where the colour of each vertex is in its list.

The authors ask whether excluding cycles of lengths 4 to 7, or even 4 to 6, forces a planar graph to
be 3-choosable.

The proposition states the positive answer to the first question: every planar graph without cycles
of lengths 4, 5, 6 and 7 is 3-choosable.  The positive answer to the second question, which would be
stronger, is not part of the statement.

Encoding.  Graphs are finite and simple.  Cycles need not be induced.  Planarity is the absence
of minors K_5 and K_3,3 (Wagner's theorem). *)

From GraphTheory Require Import digraph sgraph minor.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

Section Cycles.
Variables (T : eqType) (r : rel T).
Implicit Types c : seq T.

(** [c] is a cycle (without repetition, of length at least 3) of the relation [r]. *)
Definition seq_cycle c : bool := ucycleb r c && (2 < size c).

End Cycles.

(** [G] has no cycle whose length is between [lo] and [hi]. *)
Definition no_cycle_length_between (G : sgraph) (lo hi : nat) : Prop :=
  forall c : seq G, seq_cycle (--) c -> lo <= size c -> size c <= hi -> False.

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

(** ** Definitions copied from GraphLib/topological.v *)

(** [G] is planar: it has no minor [K_5] or [K_3,3]. *)
Definition planar (G : sgraph) : Prop :=
  ~ minor G 'K_5 /\ ~ minor G (KB 3 3).

(** ** Statement *)

Definition AX_planar_c4_c7_free_3_choosable : Prop :=
  forall G : sgraph,
    planar G -> no_cycle_length_between G 4 7 -> choosable G 3.
