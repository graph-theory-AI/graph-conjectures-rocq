(** * Chromatic number of random lifts of K_5

Amit, Linial, Matoušek, "Random lifts of graphs III: independence and chromatic number", Random
Structures Algorithms 20 (2002); Open Problem Garden,
chromatic_number_of_random_lifts_of_complete_graphs.

An h-lift of a graph G is a graph with vertex set V(G) × {1, ..., h} whose edges form a perfect
matching between {u} × {1, ..., h} and {v} × {1, ..., h} for each edge uv of G, and which has no
other edge.  A random h-lift of G is chosen uniformly among the h-lifts of G.

Question: is the chromatic number of a random h-lift of K_5 concentrated on a single value (which
may be 3 or 4) as h tends to infinity?  The proposition states the positive answer: there is a k
such that the probability that the chromatic number is k tends to 1.

Encoding.  An h-lift of K_5 is given by a permutation of {0, ..., h-1} for each pair (u,v) of
vertices of K_5; only those with u < v are used, and the unused permutations do not change the
probabilities, as each lift is given by the same number of families of permutations.  The value k
does not depend on h. *)

From GraphTheory Require Import preliminaries digraph sgraph coloring.
From mathcomp Require Import boot fingroup perm.

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

(** [P n] holds with high probability: its probability tends to 1.  The probabilities of the
    elements of the finite type [T n] are the integers [w n x], divided by their sum. *)
Definition whp
    (T : nat -> finType) (w : forall n : nat, T n -> nat)
    (P : forall n : nat, pred (T n)) : Prop :=
  forall a b : nat, 0 < a -> a <= b ->
    eventually (fun n =>
      0 < \sum_x w n x /\
      b * (\sum_(x | P n x) w n x) >= (b - a) * (\sum_x w n x)).

(** ** Definitions specific to the conjecture *)

(** The families of permutations that give the [h]-lifts of [K_5]. *)
Definition k5_lift_data (h : nat) : finType := {ffun 'I_5 * 'I_5 -> {perm 'I_h}}.

(** The [h]-lift given by [p]: for [u < v], the vertex [(u,i)] is adjacent to [(v, p (u,v) i)]. *)
Definition k5_lift (h : nat) (p : k5_lift_data h) : sgraph :=
  @sgraph_of_rel ('I_5 * 'I_h)%type
    (fun a b => (val a.1 < val b.1) && (b.2 == p (a.1, b.1) a.2)).

(** ** Statement *)

Definition OPG_random_lift_k5_chromatic_concentration : Prop :=
  exists k : nat,
    whp (fun (h : nat) (_ : k5_lift_data h) => 1) (fun h p => χ([set: k5_lift p]) == k).
