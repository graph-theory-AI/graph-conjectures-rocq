(** * Fair representation of an edge partition by a matching

Aharoni, Alon, Berger, Chudnovsky, Kotlar, Loebl, Ziv, "Fair representation by independent sets",
arXiv:1611.03196, Conjecture 1.14 (1611.03196__02).

Conjecture: if the edge set of a graph H is partitioned into sets E_1, ..., E_m, then there exists a
matching M satisfying |M ∩ E_i| >= ⌊|E_i| / (Δ(H) + 2)⌋ for all i <= m.

Encoding.  Graphs are finite and simple.  The sets E_i may be empty, which does not matter. *)

From GraphTheory Require Import digraph sgraph connectivity.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

(** The maximum degree of [G] (0 if [G] is empty). *)
Definition Delta (G : sgraph) : nat := \max_(x : G) #|N(x)|.

(** ** Definitions copied from GraphLib/packing.v *)

(** The sets [E i] (possibly empty) form a partition of the edges of [G]. *)
Definition edge_partition (G : sgraph) (m : nat) (E : 'I_m -> {set {set G}}) : Prop :=
  (forall e : {set G}, (e \in E(G)) = [exists i : 'I_m, e \in E i]) /\
  forall i j : 'I_m, i != j -> [disjoint E i & E j].

(** ** Statement *)

Definition AX_fair_representation_matching_delta_plus_2 : Prop :=
  forall (m : nat) (H : sgraph) (E : 'I_m -> {set {set H}}),
    edge_partition E ->
    exists M : {set {set H}},
      matching M /\ forall i : 'I_m, #|E i| %/ (Delta H + 2) <= #|M :&: E i|.
