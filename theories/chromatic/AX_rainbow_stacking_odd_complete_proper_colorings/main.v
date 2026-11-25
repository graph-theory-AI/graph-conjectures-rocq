(** * Rainbow stackings of proper edge colourings of complete graphs

Alon, Defant, Kravitz, "Rainbow stackings of random edge-colorings", arXiv:2405.14795, Question 3.3
(2405.14795__01).

A rainbow stacking of two edge colourings χ_1 and χ_2 of K_n is a pair (σ_1,σ_2) of permutations of
the vertices such that χ_1(σ_1^-1(e)) and χ_2(σ_2^-1(e)) are distinct for every edge e.

Question 3.3: is it true that, when n is odd, every pair of proper edge colourings of K_n has a
rainbow stacking?  The positive answer is stated.

Encoding.  Both colourings use the same set of r colours, where r is arbitrary.  An edge colouring
is a map on the sets of vertices, and its values on the sets that are not edges are irrelevant. *)

From GraphTheory Require Import digraph sgraph.
From mathcomp Require Import boot fingroup perm.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/chromatic.v *)

(** [col] is a proper edge colouring. *)
Definition proper_edge_coloring (G : sgraph) (C : eqType) (col : {set G} -> C) : Prop :=
  forall x y z : G, x -- y -> x -- z -> y != z -> col [set x; y] != col [set x; z].

(** ** Definitions specific to the conjecture *)

(** [(s1, s2)] is a rainbow stacking of [chi1] and [chi2]. *)
Definition rainbow_stacking (n r : nat) (chi1 chi2 : {set 'K_n} -> 'I_r)
    (s1 s2 : {perm 'I_n}) : Prop :=
  forall i j : ('K_n), i -- j ->
    chi1 [set (s1^-1)%g i; (s1^-1)%g j] != chi2 [set (s2^-1)%g i; (s2^-1)%g j].

(** ** Statement *)

Definition AX_rainbow_stacking_odd_complete_proper_colorings : Prop :=
  forall (n r : nat) (chi1 chi2 : {set 'K_n} -> 'I_r),
    odd n -> proper_edge_coloring chi1 -> proper_edge_coloring chi2 ->
    exists s1 s2 : {perm 'I_n}, rainbow_stacking chi1 chi2 s1 s2.
