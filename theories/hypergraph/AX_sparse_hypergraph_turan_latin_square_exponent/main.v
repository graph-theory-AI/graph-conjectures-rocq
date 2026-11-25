(** * Turán exponents of Latin square hypergraphs

Fox, Sankar, Simkin, Tidor, Zhou, "Ramsey and Turán numbers of sparse hypergraphs",
arXiv:2401.00359, Conjecture 6.4 (2401.00359__02).

A Latin square of order d is a d × d array with entries in [d] = {1, ..., d} such that each row and
each column is a permutation.  Given a Latin square L, the hypergraph H_L has vertex set
[d] ⊔ [d] ⊔ [d] and its edges are the triples (i, j, L(i,j)).  The Turán number ex(n,H) is the
maximum number of edges of a 3-uniform hypergraph on n vertices without any copy of H.

Conjecture 6.4: ex(n,H_L) = n^(3 - Θ(1/d)) for every Latin square L of order d.

Encoding.  There are absolute constants a > 0 and c > 0 such that, for every L of order d, the
inequalities n^(3 - a/d) <= ex(n,H_L) <= n^(3 - c/d) hold for all large enough n.  As a can be
increased and c decreased, a is an integer and c = 1/b for a positive integer b.  The first
inequality is raised to the power d and the second one to the power b d, and the exponents are then
made positive.  d >= 2 is assumed, as H_L has only one edge when d = 1. *)

From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

(** [P n] holds for every sufficiently large [n]. *)
Definition eventually (P : nat -> Prop) : Prop :=
  exists N : nat, forall n : nat, N <= n -> P n.

(** ** Definitions copied from GraphLib/hypergraph.v *)

(** [E] contains a copy of [F]. *)
Definition hg_contains (S T : finType) (F : {set {set S}}) (E : {set {set T}}) : bool :=
  [exists f : {ffun S -> T},
     injectiveb f && [forall e in F, [set f x | x in e] \in E]].

(** The Turán number of [F]: the maximum number of edges of a [k]-uniform hypergraph on [n]
    vertices without any copy of [F]. *)
Definition hg_turan_number (S : finType) (F : {set {set S}}) (k n : nat) : nat :=
  \max_(E : {set {set 'I_n}} | [forall e in E, #|e| == k] && ~~ hg_contains F E) #|E|.

(** [L] is a Latin square of order [d]: the rows and columns are permutations. *)
Definition latin_square (d : nat) (L : 'I_d -> 'I_d -> 'I_d) : Prop :=
  (forall i : 'I_d, injective (L i)) /\ (forall j : 'I_d, injective (fun i => L i j)).

(** ** Definitions specific to the conjecture *)

(** The hypergraph [H_L]. *)
Definition latin_hypergraph (d : nat) (L : 'I_d -> 'I_d -> 'I_d) :
    {set {set 'I_d + 'I_d + 'I_d}} :=
  [set [set inl (inl i); inl (inr j); inr (L i j)] | i : 'I_d, j : 'I_d].

(** ** Statement *)

Definition AX_sparse_hypergraph_turan_latin_square_exponent : Prop :=
  exists a b : nat,
    [/\ 0 < a, 0 < b &
        forall (d : nat) (L : 'I_d -> 'I_d -> 'I_d),
          2 <= d -> latin_square L ->
          eventually (fun n =>
            n ^ (3 * d) <= hg_turan_number (latin_hypergraph L) 3 n ^ d * n ^ a /\
            hg_turan_number (latin_hypergraph L) 3 n ^ (b * d) * n <= n ^ (3 * (b * d)))].
