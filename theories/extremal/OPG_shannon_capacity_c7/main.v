(** * Shannon capacity of the seven-cycle

Open Problem Garden, shannon_capacity_of_the_seven_cycle.

The n-th strong power G^n of a graph G has the n-tuples of vertices of G as vertices, and distinct
tuples are adjacent when their components are equal or adjacent at each position.  The Shannon
capacity of G is Θ(G) = lim α(G^n)^(1/n), where α is the independence number.  It is also the
supremum of these numbers for n >= 1.  Lovász proved that Θ(C_5) = √5.

Problem: what is the Shannon capacity of the 7-cycle C_7?

What is stated is that Θ(C_7) is an algebraic number, as Θ(C_5).

Encoding.  The problem suggests no value for Θ(C_7), so the proposition is only a proxy.  It is
incomparable with a determination of Θ(C_7): it does not give the value, and it is not implied by a
determination of Θ(C_7) as a transcendental number.  "Θ(C_7) is algebraic" is expressed by: each
archimedean real closed field contains a number c that is the Shannon capacity of C_7, i.e. the
least c such that α(C_7^n) <= c^n for every n >= 1.  Indeed, in an archimedean field such a c is the
real number Θ(C_7), and the smallest archimedean real closed field is the field of real algebraic
numbers. *)

From GraphTheory Require Import preliminaries digraph sgraph coloring.
From mathcomp Require Import boot order algebra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.Theory GRing.Theory Num.Theory.

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

(** The cycle on [n] vertices ([3 <= n] is meant). *)
Definition cycle_graph (n : nat) : sgraph :=
  sgraph_of_rel (fun i j : 'I_n => (val i).+1 %% n == val j).

(** ** Definitions copied from GraphLib/extremal.v *)

(** The [n]-th strong power of [G]: distinct tuples whose components are equal or adjacent are
    adjacent. *)
Definition strong_power (G : sgraph) (n : nat) : sgraph :=
  @sgraph_of_rel {ffun 'I_n -> G} (fun x y => [forall i, (x i == y i) || (x i -- y i)]).

(** The Shannon capacity of [G] is [c], the least upper bound of [alpha(G^n)^(1/n)]. *)
Definition shannon_capacity (R : realFieldType) (G : sgraph) (c : R) : Prop :=
  (forall n, (0 < n)%N -> (α([set: strong_power G n])%:R <= c ^+ n)%R) /\
  (forall b : R, (forall n, (0 < n)%N -> (α([set: strong_power G n])%:R <= b ^+ n)%R) ->
     (c <= b)%R).

(** ** Statement *)

Definition proxy_OPG_shannon_capacity_c7 : Prop :=
  forall R : archiRcfType, exists c : R, shannon_capacity (cycle_graph 7) c.
