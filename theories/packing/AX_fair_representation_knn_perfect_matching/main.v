(** * Almost fair representation of a partition of E(K_{n,n}) by a perfect matching

Aharoni, Alon, Berger, Chudnovsky, Kotlar, Loebl, Ziv, "Fair representation by independent sets",
arXiv:1611.03196, Conjecture 1.9 (1611.03196__01).

Conjecture: for any partition E_1, ..., E_m of E(K_{n,n}) and any j <= m there exists a perfect
matching F in K_{n,n} satisfying |F ∩ E_i| >= ⌊|E_i| / n⌋ for all i <> j, and
|F ∩ E_j| >= ⌊|E_j| / n⌋ - 1.

Encoding.  It is assumed that n >= 1, as one divides by n.  The sets E_i may be empty, which does
not matter.  The subtraction is truncated at 0. *)

From GraphTheory Require Import digraph sgraph connectivity.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/packing.v *)

(** [M] is a perfect matching. *)
Definition perfect_matching (G : sgraph) (M : {set {set G}}) : Prop :=
  matching M /\ cover M = [set: G].

(** The sets [E i] (possibly empty) form a partition of the edges of [G]. *)
Definition edge_partition (G : sgraph) (m : nat) (E : 'I_m -> {set {set G}}) : Prop :=
  (forall e : {set G}, (e \in E(G)) = [exists i : 'I_m, e \in E i]) /\
  forall i j : 'I_m, i != j -> [disjoint E i & E j].

(** ** Statement *)

Definition AX_fair_representation_knn_perfect_matching : Prop :=
  forall (n m : nat) (E : 'I_m -> {set {set KB n n}}) (j : 'I_m),
    0 < n -> edge_partition E ->
    exists F : {set {set KB n n}},
      [/\ perfect_matching F,
          (forall i : 'I_m, i != j -> #|E i| %/ n <= #|F :&: E i|)
        & #|E j| %/ n - 1 <= #|F :&: E j|].
