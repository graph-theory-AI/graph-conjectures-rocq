(** * Choosability of K_{s,t}-minor-free graphs: the bound 2s + t

Steiner, "Disproof of a conjecture by Woodall", arXiv:2201.09115, Question 2 (2201.09115__01).

A graph G is k-choosable if, whenever each vertex has a list of at least k colours, there is a
proper colouring where each vertex has a colour of its list.  The list chromatic number χ_l(G) is
the least such k.

Question 2: is it true that, for all integers 1 <= s <= t, every graph G with no K_{s,t} minor
satisfies χ_l(G) <= 2s + t?

Encoding.  Graphs are finite and simple.  The proposition states the positive answer.
"χ_l(G) <= m" is written: if [ch] is the list chromatic number of G then [ch <= m]. *)

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

Definition AX_kst_minor_free_choosable_2s_t : Prop :=
  forall (s t ch : nat) (G : sgraph),
    1 <= s -> s <= t -> ~ minor G (KB s t) -> choice_number G ch -> ch <= 2 * s + t.
