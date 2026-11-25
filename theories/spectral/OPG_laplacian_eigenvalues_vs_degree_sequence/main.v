(** * Laplacian degrees of a graph

Guo, "On the third largest Laplacian eigenvalue of a graph", Linear and Multilinear Algebra 55
(2007); Open Problem Garden, laplacian_degrees_of_a_graph.

The Laplacian matrix of a graph G is L = D - A, where D is the diagonal matrix of the degrees and
A is the adjacency matrix.  Let t_k be the k-th largest eigenvalue of L, with multiplicities,
and let d_k(G) be the k-th largest degree of G.  The k-th Laplacian degree of G is
c_k(G) = t_k + k - 2.

Conjecture: if G is a connected graph on n vertices, then c_k(G) >= d_k(G) for
k = 1, 2, ..., n-1.

Encoding.  The eigenvalues are in an arbitrary real closed field R (for example, the real
numbers).  The lists s of the eigenvalues and d of the degrees are in nonincreasing order and
indexed from 0: t_k and d_k(G) are their entries of index k-1. *)

From GraphTheory Require Import digraph sgraph.
From mathcomp Require Import boot order algebra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

(** The degrees of the vertices of [G]. *)
Definition degree_sequence (G : sgraph) : seq nat := [seq #|N(v)| | v : G].

(** ** Definitions copied from GraphLib/spectral.v *)

Local Open Scope ring_scope.

Section Matrices.
Variable R : nzRingType.

(** The adjacency matrix of [G]. *)
Definition adjacency_mx (G : sgraph) : 'M[R]_(#|G|) :=
  \matrix_(i, j) (if enum_val i -- enum_val j then 1 else 0).

(** The diagonal matrix of the degrees. *)
Definition degree_mx (G : sgraph) : 'M[R]_(#|G|) :=
  diag_mx (\row_i #|N(enum_val i)|%:R).

(** The Laplacian matrix of [G]. *)
Definition laplacian_mx (G : sgraph) : 'M[R]_(#|G|) := degree_mx G - adjacency_mx G.

End Matrices.

Section RealSpectrum.
Variable R : rcfType.

(** [s] is the list of the eigenvalues of [A] with multiplicities, in nonincreasing order. *)
Definition is_spectrum (n : nat) (A : 'M[R]_n) (s : seq R) : Prop :=
  [/\ size s = n, sorted (fun x y : R => y <= x) s
    & char_poly A = \prod_(x <- s) ('X - x%:P)].

End RealSpectrum.

(** ** Statement *)

Definition OPG_laplacian_eigenvalues_vs_degree_sequence : Prop :=
  forall (R : rcfType) (G : sgraph),
    connected [set: G] ->
    forall s : seq R, is_spectrum (laplacian_mx R G) s ->
    let d := sort geq (degree_sequence G) in
    forall k : nat, (1 <= k <= #|G| - 1)%N ->
      (nth 0%N d k.-1)%:R <= nth 0 s k.-1 + k%:R - 2%:R.
