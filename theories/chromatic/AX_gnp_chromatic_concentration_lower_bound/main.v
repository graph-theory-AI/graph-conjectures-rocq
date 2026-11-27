(** * Non-concentration of the chromatic number of random graphs

Scott, "On the concentration of the chromatic number of random graphs", arXiv:0806.0178, open
problem (0806.0178__00).

The random graph G(n,p) has n vertices, and each pair is an edge independently with probability p;
here 0 < p < 1 is fixed.  The chromatic number is concentrated in an interval of length l if there
is a function h such that |χ(G(n,p)) - h(n)| < l with probability 1 - o(1).

Problem: show that, for p fixed, the chromatic number of G(n,p) is not concentrated in an interval
of constant length.

The proposition states that, for every p and c, the chromatic number of G(n,p) is not concentrated
on c + 1 consecutive integers: there is no function s such that s(n) <= χ(G(n,p)) <= s(n) + c with
probability 1 - o(1).

Encoding.  The random graph is given by its edge set on {0,...,n-1}.  The real numbers are
represented by an arbitrary archimedean ordered field R, that is, up to isomorphism, by an
arbitrary subfield of the reals (possibly the reals).  As l and c are arbitrary constants, intervals
of length l and c + 1 consecutive integers give equivalent statements. *)

From GraphTheory Require Import preliminaries digraph sgraph coloring.
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

(** ** Definitions copied from GraphLib/random.v *)

(** The probability that the edge set of the random graph [G(n,p)] on [0, ..., n-1] satisfies
    [P]. *)
Definition gnp_probability (R : realFieldType) (p : R) (n : nat) (P : pred {set {set 'I_n}}) : R :=
  (\sum_(E : {set {set 'I_n}} | (E \subset E('K_n)) && P E)
    p ^+ #|E| * (1 - p) ^+ (#|E('K_n)| - #|E|))%R.

(** The edge set of the random graph [G(n,p)] satisfies [P n] with high probability. *)
Definition gnp_whp (R : realFieldType) (p : R) (P : forall n : nat, pred {set {set 'I_n}}) : Prop :=
  forall eps : R, (0 < eps)%R -> eventually (fun n => (1 - eps <= gnp_probability p (P n))%R).

(** ** Definitions specific to the conjecture *)

Local Open Scope ring_scope.

(** The chromatic number of the graph with edge set [E] is between [s] and [s + c]. *)
Definition chi_in_interval (n c s : nat) (E : {set {set 'I_n}}) : bool :=
  let G := sgraph_of_edges E in (s <= χ([set: G]) <= s + c)%N.

(** For some function [s], the chromatic number of [G(n,p)] is one of [s n, ..., s n + c] with
    probability tending to 1 when [n] tends to infinity. *)
Definition chi_concentrated (R : realFieldType) (p : R) (c : nat) : Prop :=
  exists s : nat -> nat,
    gnp_whp p (fun n (E : {set {set 'I_n}}) => chi_in_interval c (s n) E).

(** ** Statement *)

Definition AX_gnp_chromatic_concentration_lower_bound : Prop :=
  forall (R : archiRealFieldType) (p : R),
    0 < p < 1 -> forall c : nat, ~ chi_concentrated p c.
