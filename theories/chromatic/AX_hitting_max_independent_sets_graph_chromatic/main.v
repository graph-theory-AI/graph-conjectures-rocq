(** * Chromatic number of the graph of nearly opposite binary vectors

Alon, "Hitting all maximum independent sets", arXiv:2103.05998, concluding remarks
(2103.05998__00).

Let m be even and t be a positive integer with 4t^2 <= m.  Let G_{m,t} be the graph whose vertices
are the binary vectors of length m, two of them being adjacent if their Hamming distance (the number
of coordinates where they differ) exceeds m - 2t.

Conjecture: the chromatic number of G_{m,t} is Θ(t^2).

Encoding.  The constants in Θ are uniform over the pairs (m,t).  They are k and 1/k for an integer
k > 0, which is not a restriction.  Binary vectors are functions from {0,...,m-1} to the
booleans. *)

From GraphTheory Require Import preliminaries digraph sgraph coloring.
From mathcomp Require Import boot.

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

(** ** Definitions specific to the conjecture *)

(** G_{m,t} (the subtraction is exact when [4 * t ^ 2 <= m]). *)
Definition far_vectors_graph (m t : nat) : sgraph :=
  sgraph_of_rel (fun u v : {ffun 'I_m -> bool} => m - 2 * t < #|[set i | u i != v i]|).

(** ** Statement *)

Definition AX_hitting_max_independent_sets_graph_chromatic : Prop :=
  exists k : nat, 0 < k /\
    forall m t : nat, 0 < t -> ~~ odd m -> 4 * t ^ 2 <= m ->
      t ^ 2 <= k * χ([set: far_vectors_graph m t]) /\
      χ([set: far_vectors_graph m t]) <= k * t ^ 2.
