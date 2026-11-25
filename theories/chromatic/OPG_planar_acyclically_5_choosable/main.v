(** * Acyclic list colouring of planar graphs

Borodin, Fon-Der-Flaass, Kostochka, Raspaud, Sopena, "Acyclic list 7-coloring of planar graphs",
J. Graph Theory 40 (2002); Open Problem Garden, acyclic_list_colouring_of_planar_graphs.

A colouring of a graph is acyclic if it is proper and each cycle has at least three colours.  A
graph is acyclically k-choosable if it has an acyclic colouring from all lists of at least k colours
on its vertices.

Conjecture: every planar graph is acyclically 5-choosable.

Encoding.  Graphs are finite and simple.  Planarity is defined by excluded minors (Wagner's
theorem).  Cycles are cyclic sequences of at least 3 distinct vertices. *)

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

(** ** Definitions copied from GraphLib/chromatic.v *)

(** [f] is a proper colouring from the lists [L]. *)
Definition proper_list_coloring
    (G : sgraph) (C : finType) (L : G -> {set C}) (f : G -> C) : Prop :=
  (forall v : G, f v \in L v) /\
  (forall x y : G, x -- y -> f x != f y).

(** [f] is an acyclic colouring from the lists [L]. *)
Definition acyclic_list_coloring (G : sgraph) (C : finType) (L : G -> {set C})
    (f : G -> C) : Prop :=
  proper_list_coloring L f /\
  forall c : seq G, seq_cycle (--) c -> 2 < size (undup [seq f x | x <- c]).

(** [G] is acyclically [k]-choosable. *)
Definition acyclically_choosable (G : sgraph) (k : nat) : Prop :=
  forall (C : finType) (L : G -> {set C}),
    (forall v : G, k <= #|L v|) ->
    exists f : G -> C, acyclic_list_coloring L f.

(** ** Definitions copied from GraphLib/topological.v *)

(** [G] is planar: it has no minor [K_5] or [K_3,3]. *)
Definition planar (G : sgraph) : Prop :=
  ~ minor G 'K_5 /\ ~ minor G (KB 3 3).

(** ** Statement *)

Definition OPG_planar_acyclically_5_choosable : Prop :=
  forall G : sgraph, planar G -> acyclically_choosable G 5.
