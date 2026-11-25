(** * List colouring analogue of Reed's conjecture

Bonamy, Kelly, Nelson, Postle, "Bounding χ by a fraction of Δ for graphs without large cliques",
arXiv:1803.01051 (1803.01051__01).

A graph G is k-choosable if it has a proper colouring from all lists of at least k colours on its
vertices.  The list chromatic number (or choice number) χ_l(G) is the minimum k such that G is
k-choosable.

Reed's conjecture may also be true for the list chromatic number, i.e., χ_l(G) <= ⌈(Δ + 1 + ω) / 2⌉
for every graph G of maximum degree at most Δ with no clique of size greater than ω.

Encoding.  Graphs are finite and simple.  Δ and ω are the maximum degree and the clique number of G,
without loss of generality.  "χ_l(G) = m" is a relation between G and m. *)

From GraphTheory Require Import digraph sgraph coloring.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

(** The ceiling of [a / b] (0 if [b = 0]). *)
Definition ceil_div (a b : nat) : nat := (a + b - 1) %/ b.

(** The maximum degree of [G] (0 if [G] is empty). *)
Definition Delta (G : sgraph) : nat := \max_(x : G) #|N(x)|.

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

Definition AX_list_chromatic_reed_bound : Prop :=
  forall (G : sgraph) (m : nat),
    choice_number G m -> m <= ceil_div (Delta G + 1 + ω([set: G])) 2.
