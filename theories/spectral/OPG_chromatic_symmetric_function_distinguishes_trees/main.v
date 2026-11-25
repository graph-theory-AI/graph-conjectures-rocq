(** * The chromatic symmetric function distinguishes trees

Stanley, "A symmetric function generalization of the chromatic polynomial of a graph", Advances in
Mathematics 111 (1995); Open Problem Garden,
does_the_symmetric_chromatic_function_distinguish_trees.

The chromatic symmetric function of a graph G is X_G = Σ_f Π_v x_{f(v)}, where f ranges over the
proper colourings of G by positive integers, v over the vertices of G, and x_1, x_2, ... are
commuting indeterminates.  The coefficient of x_1^{d_1} x_2^{d_2} ... in X_G is the number of
proper colourings of G with exactly d_i vertices of colour i, for each i.

Problem: do there exist nonisomorphic trees with the same chromatic symmetric function?

The proposition states the negative answer: any two trees with the same chromatic symmetric
function are isomorphic.

Encoding.  Two graphs have the same chromatic symmetric function if, for every k and all natural
numbers a_0, ..., a_{k-1}, they have the same number of proper colourings by {0,...,k-1} with
a_i vertices of colour i, for each i. *)

From GraphTheory Require Import digraph sgraph coloring.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/chromatic.v *)

(** [col] is a proper colouring of [G]. *)
Definition proper_coloring (G : sgraph) (C : finType) (col : G -> C) : bool :=
  coloring (preim_partition col [set: G]) [set: G].

(** The coefficient of [x_0^(a 0) x_1^(a 1) ...] in the chromatic symmetric function of [G]
    with [k] variables: the number of proper colourings with [a i] vertices of colour [i]. *)
Definition chromatic_symmetric_coeff (G : sgraph) (k : nat) (a : 'I_k -> nat) : nat :=
  #|[set c : {ffun G -> 'I_k} |
       proper_coloring c && [forall b : 'I_k, #|[set x | c x == b]| == a b]]|.

(** [G] and [H] have the same chromatic symmetric function. *)
Definition same_chromatic_symmetric (G H : sgraph) : Prop :=
  forall (k : nat) (a : 'I_k -> nat), chromatic_symmetric_coeff G a = chromatic_symmetric_coeff H a.

(** ** Statement *)

Definition OPG_chromatic_symmetric_function_distinguishes_trees : Prop :=
  forall T1 T2 : sgraph,
    is_tree [set: T1] -> is_tree [set: T2] -> same_chromatic_symmetric T1 T2 ->
    inhabited (T1 ≃ T2).
