(** * Normality of random graphs

Gajser, Mohar, "Minimal normal graph covers", arXiv:1601.01129, open question (1601.01129__01).

A graph G is normal if there are a set K of cliques and a set A of stable sets, each covering
the vertices of G, such that every clique of K meets every stable set of A.

The random graph G(n,p) has n vertices, and each pair of vertices is an edge with probability p,
independently.

Question: are random graphs G(n,p) normal with high probability?

The proposition states the positive answer, for every fixed real number p such that 0 < p < 1:
the probability that G(n,p) is normal tends to 1 when n tends to infinity.

Encoding.  The random graph is given by its edge set on {0,...,n-1}.  The real numbers are
represented by an arbitrary archimedean ordered field R, that is, up to isomorphism, by an
arbitrary subfield of the reals (possibly the reals). *)

From GraphTheory Require Import preliminaries digraph sgraph.
From GraphTheory Require dom.
From mathcomp Require Import boot order algebra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

(** [P n] holds for every sufficiently large [n]. *)
Definition eventually (P : nat -> Prop) : Prop :=
  exists N : nat, forall n : nat, N <= n -> P n.

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

(** [G] is normal (Koerner): it has a set [K] of cliques and a set [A] of stable sets, both
    covering the vertices, such that each clique of [K] meets each stable set of [A]. *)
Definition normal_graph (G : sgraph) : bool :=
  [exists K : {set {set G}},
    [exists A : {set {set G}},
      [forall C in K, cliqueb C] &&
      [forall S in A, dom.stable S] &&
      [forall v : G, [exists C in K, v \in C]] &&
      [forall v : G, [exists S in A, v \in S]] &&
      [forall C in K, [forall S in A, C :&: S != set0]]]].

(** ** Definitions copied from GraphLib/random.v *)

(** The probability that the edge set of the random graph [G(n,p)] on [0, ..., n-1] satisfies
    [P]. *)
Definition gnp_probability (R : realFieldType) (p : R) (n : nat) (P : pred {set {set 'I_n}}) : R :=
  (\sum_(E : {set {set 'I_n}} | (E \subset E('K_n)) && P E)
    p ^+ #|E| * (1 - p) ^+ (#|E('K_n)| - #|E|))%R.

(** The edge set of the random graph [G(n,p)] satisfies [P n] with high probability. *)
Definition gnp_whp (R : realFieldType) (p : R) (P : forall n : nat, pred {set {set 'I_n}}) : Prop :=
  forall eps : R, (0 < eps)%R -> eventually (fun n => (1 - eps <= gnp_probability p (P n))%R).

(** ** Statement *)

Definition AX_normal_graphs_random_gnp_whp : Prop :=
  forall (R : archiRealFieldType) (p : R),
    (0 < p < 1)%R -> gnp_whp p (fun n (E : {set {set 'I_n}}) => normal_graph (sgraph_of_edges E)).
