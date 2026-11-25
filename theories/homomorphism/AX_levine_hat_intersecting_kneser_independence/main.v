(** * Independent sets in cartesian powers of Kneser graphs

Alon, Friedgut, Kalai, Kindler, "The success probability in Levine's hat problem, and independent
sets in graphs", arXiv:2208.06858, Conjecture 2.6 (2208.06858__02).

The Kneser graph K(n) has vertex set {0,1}^n, with x and y adjacent if their supports are disjoint
(there is no i with x_i = y_i = 1).  The cartesian (or Hamming) power G^t of a graph G has vertex
set V(G)^t, two tuples being adjacent if they differ in exactly one coordinate and are adjacent in G
in this coordinate.  The independence ratio of G is α(G)/|V(G)|.

Conjecture: the limit, when t tends to infinity, of the limit, when n tends to infinity, of the
independence ratio of K(n)^t is 0.

Encoding.  The vertices of K(n) are the subsets of {0,...,n-1}, and distinct subsets are adjacent if
they are disjoint.  The empty set thus has no loop, although it belongs to no intersecting family.
This does not change the limits, since the tuples with an empty coordinate are a fraction at most
t/2^n of the vertices.  Limits are written without quotients: for every q >= 1, if t is large enough
then, if n is large enough, the independence ratio is at most 1/q.  The existence of the inner limit
is not stated, as it always exists: the independence ratio is nondecreasing in n, up to the above
fraction. *)

From GraphTheory Require Import preliminaries digraph sgraph coloring.
From mathcomp Require Import boot.

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

Section Products.
Variables G H : sgraph.

(** Equal in one coordinate and adjacent in the other. *)
Definition box_rel : rel (G * H) :=
  fun p q => ((p.1 == q.1) && (p.2 -- q.2)) || ((p.2 == q.2) && (p.1 -- q.1)).

Lemma box_sym : symmetric box_rel.
Proof.
by move=> p q; rewrite /box_rel ![p.1 == q.1]eq_sym ![p.2 == q.2]eq_sym
   ![p.1 -- q.1]sg_sym' ![p.2 -- q.2]sg_sym'.
Qed.

Lemma box_irrefl : irreflexive box_rel.
Proof. by move=> p; rewrite /box_rel !eqxx /= !sg_irrefl. Qed.

(** The cartesian product of [G] and [H]. *)
Definition cartesian_product : sgraph := SGraph box_sym box_irrefl.

End Products.

(** ** Definitions copied from GraphLib/homomorphism.v *)

(** The [t]-th cartesian power of [G] ([K_1] for [t = 0]). *)
Fixpoint cartesian_power (G : sgraph) (t : nat) : sgraph :=
  if t is t'.+1 then cartesian_product (cartesian_power G t') G else 'K_1.

(** ** Definitions specific to the conjecture *)

(** The Kneser graph K(n): distinct subsets of [0, ..., n-1] are adjacent if disjoint. *)
Definition kneser_graph (n : nat) : sgraph :=
  sgraph_of_rel (fun A B : {set 'I_n} => [disjoint A & B]).

(** ** Statement *)

Definition AX_levine_hat_intersecting_kneser_independence : Prop :=
  forall q : nat, 0 < q ->
    eventually (fun t => eventually (fun n =>
      let G := cartesian_power (kneser_graph n) t in q * α([set: G]) <= #|G|)).
