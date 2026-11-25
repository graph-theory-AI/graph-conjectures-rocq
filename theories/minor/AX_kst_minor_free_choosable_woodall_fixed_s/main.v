(** * Woodall's conjecture for fixed s

Steiner, "Disproof of a conjecture by Woodall", arXiv:2201.09115, open problem (2201.09115__02).

A graph is k-choosable if, whenever each vertex has a list of at least k colours, there is a proper
colouring where the colour of each vertex is in its list.  The choice number is the least such k.

Open problem: does Woodall's conjecture, that every graph without K_s,t minor is
(s + t - 1)-choosable, remain true if s is fixed and t is sufficiently large in terms of s?

The proposition states the positive answer: for every s >= 1 there exists T such that, for t >= T,
every graph without K_s,t minor has choice number at most s + t - 1.

Encoding.  Graphs are finite and simple.  T is chosen at least s, without loss of generality. *)

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

Definition AX_kst_minor_free_choosable_woodall_fixed_s : Prop :=
  forall s : nat, 1 <= s ->
    exists T : nat,
      s <= T /\
      forall (t ch : nat) (G : sgraph),
        T <= t ->
        ~ minor G (KB s t) ->
        choice_number G ch ->
        ch <= s + t - 1.
