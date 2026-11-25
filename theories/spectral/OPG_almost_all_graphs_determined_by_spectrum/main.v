(** * Are almost all graphs determined by their spectrum?

van Dam, Haemers, "Which graphs are determined by their spectrum?", Linear Algebra and its
Applications 373 (2003); Open Problem Garden, are_almost_all_graphs_determined_by_their_spectrum.

Two graphs are cospectral if their adjacency matrices have the same eigenvalues with the same
multiplicities.  A graph is determined by its spectrum if every graph cospectral with it is
isomorphic to it.

Problem: are almost all graphs determined by their spectrum?

The proposition states the positive answer: the proportion of the labelled graphs on n vertices
that are determined by their spectrum tends to 1 when n tends to infinity.  In other words, for
every positive integer m, at most a fraction 1/m of them are not determined by their spectrum
when n is large enough.

Encoding.  A labelled graph on n vertices is a graph on {0,...,n-1}, given by its edge set.
Graphs are cospectral if the characteristic polynomials of their adjacency matrices, over the
integers, are equal.  It suffices to compare graphs with the same number of vertices, since
cospectral graphs have the same order.  Labelled graphs are counted, not
isomorphism classes; the two proportions have the same limit, as almost all graphs have no
nontrivial automorphism. *)

From GraphTheory Require Import preliminaries digraph sgraph.
From mathcomp Require Import boot algebra perm.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

Lemma sgraph_of_rel_sym (V : finType) (r : rel V) :
  symmetric (fun x y => (x != y) && sc r x y).
Proof. by move=> x y /=; rewrite eq_sym orbC. Qed.

Lemma sgraph_of_rel_irrefl (V : finType) (r : rel V) :
  irreflexive (fun x y => (x != y) && sc r x y).
Proof. by move=> x; rewrite eqxx. Qed.

(** The graph on [V] whose edges are given by [r], up to symmetry and loops. *)
Definition sgraph_of_rel (V : finType) (r : rel V) : sgraph :=
  SGraph (@sgraph_of_rel_sym V r) (@sgraph_of_rel_irrefl V r).

(** The relation given by a set of pairs. *)
Definition edge_set_rel (V : finType) (E : {set {set V}}) : rel V :=
  fun x y => [set x; y] \in E.

(** The graph on [V] with edge set [E]. *)
Definition sgraph_of_edges (V : finType) (E : {set {set V}}) : sgraph :=
  sgraph_of_rel (edge_set_rel E).

(** ** Definitions copied from GraphLib/spectral.v *)

Local Open Scope ring_scope.

Section Matrices.
Variable R : nzRingType.

(** The adjacency matrix of [G]. *)
Definition adjacency_mx (G : sgraph) : 'M[R]_(#|G|) :=
  \matrix_(i, j) (if enum_val i -- enum_val j then 1 else 0).

End Matrices.

(** [G] and [H] are cospectral: their adjacency matrices have the same spectrum, with
    multiplicities. *)
Definition cospectral (G H : sgraph) : bool :=
  char_poly (adjacency_mx int G) == char_poly (adjacency_mx int H).

(** The graph on [0, ..., n-1] with edge set [E] is determined by its spectrum: the graphs on
    [0, ..., n-1] cospectral with it are isomorphic to it. *)
Definition spectrum_determined (n : nat) (E : {set {set 'I_n}}) : bool :=
  [forall F : {set {set 'I_n}},
     (F \subset E('K_n)) ==> cospectral (sgraph_of_edges E) (sgraph_of_edges F) ==>
     [exists s : 'S_n, F == [set s @: e | e : {set 'I_n} in E]]].

Local Close Scope ring_scope.

(** ** Definitions specific to the conjecture *)

(** The number of labelled graphs on [n] vertices that are determined by their spectrum. *)
Definition determined_count (n : nat) : nat :=
  #|[set E in powerset E('K_n) | spectrum_determined E]|.

(** ** Statement *)

Definition OPG_almost_all_graphs_determined_by_spectrum : Prop :=
  forall m : nat, 0 < m ->
    exists N : nat, forall n : nat, N <= n ->
      m * (#|powerset E('K_n)| - determined_count n) <= #|powerset E('K_n)|.
