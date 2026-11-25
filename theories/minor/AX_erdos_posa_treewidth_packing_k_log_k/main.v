(** * Packing subgraphs of large treewidth

Aboulker, Fiorini, Huynh, Joret, Raymond, Sau, "A tight Erdős-Pósa function for wheel minors",
SIAM J. Discrete Math. 32 (2018), arXiv:1710.06282, Conjecture 1.4 (1710.06282__01).

Conjecture 1.4: there is a function f such that for all integers r, k >= 1, every graph of
treewidth at least f(r) k log(k+1) has k vertex-disjoint subgraphs of treewidth at least r.

Encoding.  Graphs are finite and simple.  The subgraphs are induced by disjoint sets of vertices;
this is equivalent, as the treewidth is monotone under taking subgraphs.  The factor log(k+1) is
replaced by 1 + ⌊log_2(k+1)⌋, which is equivalent up to a constant factor of f. *)

From GraphTheory Require Import digraph sgraph treewidth.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/minor.v *)

(** The treewidth of [G] is at most [k] (the width of a decomposition is, in GraphTheory, the
    maximum size of a bag). *)
Definition treewidth_le (G : sgraph) (k : nat) : Prop :=
  exists (T : forest) (D : T -> {set G}), sdecomp T G D /\ width D <= k.+1.

(** The treewidth of [G] is at least [k]. *)
Definition treewidth_ge (G : sgraph) (k : nat) : Prop :=
  forall m : nat, treewidth_le G m -> k <= m.

(** ** Definitions specific to the conjecture *)

(** [G] has [k] disjoint nonempty sets of vertices that induce subgraphs of treewidth at least
    [r]. *)
Definition disjoint_large_treewidth_subgraphs (G : sgraph) (r k : nat) : Prop :=
  exists S : 'I_k -> {set G},
    (forall i : 'I_k, S i != set0) /\
    (forall i j : 'I_k, i != j -> S i :&: S j = set0) /\
    forall i : 'I_k, treewidth_ge (induced (S i)) r.

(** ** Statement *)

Definition AX_erdos_posa_treewidth_packing_k_log_k : Prop :=
  exists f : nat -> nat,
    forall (r k : nat) (G : sgraph),
      1 <= r ->
      1 <= k ->
      treewidth_ge G (f r * k * (trunc_log 2 k.+1).+1) ->
      disjoint_large_treewidth_subgraphs G r k.
