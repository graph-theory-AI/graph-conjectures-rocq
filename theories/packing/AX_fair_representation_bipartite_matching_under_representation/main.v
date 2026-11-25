(** * Under-representation by a large matching in a bipartite graph

Aharoni, Alon, Berger, Chudnovsky, Kotlar, Loebl, Ziv, "Fair representation by independent sets",
arXiv:1611.03196, Conjecture 1.15 (1611.03196__03).

Conjecture: for every m there exists a number c(m) for which the following is true: if G is a
bipartite graph and E_1, ..., E_m are any sets of edges, then there exists a matching S in G of size
at least |E(G)| / Δ(G) - c(m) such that |S ∩ E_i| <= ⌈|E_i| / Δ(G)⌉ for all i <= m.

Encoding.  Graphs are finite and simple, with at least one edge, so that Δ(G) > 0.  The sets E_i may
overlap.  It suffices to consider natural numbers c(m), and to bound the size of S by
⌊|E(G)| / Δ(G)⌋ - c(m). *)

From GraphTheory Require Import digraph sgraph connectivity.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

(** The ceiling of [a / b] (0 if [b = 0]). *)
Definition ceil_div (a b : nat) : nat := (a + b - 1) %/ b.

(** The maximum degree of [G] (0 if [G] is empty). *)
Definition Delta (G : sgraph) : nat := \max_(x : G) #|N(x)|.

(** [G] is bipartite: it has a bipartition (a set [A] such that each edge has exactly one end in
    [A]). *)
Definition bipartite (G : diGraph) : Prop := exists A : {set G}, bipartition A.

(** ** Statement *)

Definition AX_fair_representation_bipartite_matching_under_representation : Prop :=
  forall m : nat, exists c : nat,
    forall (G : sgraph) (E : 'I_m -> {set {set G}}),
      bipartite G -> 0 < Delta G -> (forall i : 'I_m, E i \subset E(G)) ->
      exists S : {set {set G}},
        [/\ matching S,
            #|E(G)| %/ Delta G <= #|S| + c
          & forall i : 'I_m, #|S :&: E i| <= ceil_div #|E i| (Delta G)].
