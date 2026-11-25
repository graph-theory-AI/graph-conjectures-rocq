(** * Signing a graph to have small magnitude eigenvalues

Bilu, Linial, "Lifts, discrepancy and nearly optimal spectral gap", Combinatorica 26 (2006);
Open Problem Garden, signing_a_graph_to_have_small_magnitude_eigenvalues.

A symmetric signing of a graph G is a symmetric matrix obtained from the adjacency matrix of G
by replacing some entries 1 by -1.

Conjecture: every d-regular graph has a symmetric signing all of whose eigenvalues have
absolute value at most 2√(d-1).

Encoding.  Matrices have coefficients in an arbitrary real closed field (for example, the real
numbers).  The graph is assumed to be nonempty, and d >= 2, which is implicit in the source: the
bound is 0 for d = 1, where the conjecture fails for K_2, and is not defined for d = 0.
Only the eigenvalues in the real closed field are considered, which are all the eigenvalues
since the matrix is symmetric. *)

From GraphTheory Require Import digraph sgraph.
From mathcomp Require Import boot order algebra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

(** Every vertex has degree [d]. *)
Definition regular (G : sgraph) (d : nat) : Prop := forall v : G, #|N(v)| = d.

(** ** Definitions copied from GraphLib/spectral.v *)

Local Open Scope ring_scope.

Section RealSpectrum.
Variable R : rcfType.

(** All eigenvalues of [A] have absolute value at most [b] (real eigenvalues only: [A] is meant
    to be symmetric). *)
Definition spectral_radius_le (n : nat) (A : 'M[R]_n) (b : R) : Prop :=
  forall x : R, eigenvalue A x -> `|x| <= b.

(** [S] is a signing of the adjacency matrix of [G]: a symmetric matrix obtained by replacing
    some entries [1] by [-1]. *)
Definition is_signing (G : sgraph) (S : 'M[R]_(#|G|)) : Prop :=
  (forall i j, S i j = S j i) /\
  (forall i j, if enum_val i -- enum_val j
               then (S i j = 1) \/ (S i j = -1)
               else S i j = 0).

End RealSpectrum.

(** ** Statement *)

Definition OPG_regular_signing_eigenvalues_2_sqrt_d : Prop :=
  forall (R : rcfType) (G : sgraph) (d : nat),
    regular G d -> (2 <= d)%N -> (0 < #|G|)%N ->
    exists S : 'M[R]_(#|G|),
      is_signing S /\ spectral_radius_le S (2%:R * Num.sqrt (d.-1)%:R).
