(** * List chromatic number of K_t-minor-free graphs: the bound 2t

Steiner, "Improved lower bound for the list chromatic number of graphs with no K_t minor",
arXiv:2110.09403, Problem 1 (2110.09403__00).

A graph G is k-choosable if it has a proper colouring from all lists of at least k colours on its
vertices.  The list chromatic number (or choice number) χ_l(G) is the minimum k such that G is
k-choosable.

Problem 1: does every K_t-minor-free graph G satisfy χ_l(G) <= 2t?

The proposition states the positive answer.

Encoding.  Graphs are finite and simple.  "χ_l(G) = m" is a relation between G and m.  The
hypothesis t >= 1 is harmless: no graph is K_0-minor-free. *)

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

(** The choice number (list chromatic number) of [G] is [m]. *)
Definition choice_number (G : sgraph) (m : nat) : Prop :=
  choosable G m /\ (forall k, choosable G k -> m <= k).

(** ** Statement *)

Definition AX_kt_minor_free_list_chromatic_2t : Prop :=
  forall (t m : nat) (G : sgraph),
    1 <= t -> ~ minor G 'K_t -> choice_number G m -> m <= 2 * t.
