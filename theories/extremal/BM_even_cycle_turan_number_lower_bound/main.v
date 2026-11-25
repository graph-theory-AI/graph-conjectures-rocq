(** * Turán number of even cycles

Erdős; Bondy, Murty, "Graph Theory", Appendix A, problem 34.

The Turán number ex(n, C_2k) is the maximum number of edges of a simple graph with n vertices that
contains no cycle of length 2k as a subgraph.

Conjecture: for every k >= 2, there is a positive constant c such that
ex(n, C_2k) >= c n^(1 + 1/k).

Encoding.  The inequality is stated for large n, as ex(1, C_2k) = 0; this is equivalent to stating
it for all n >= 2, where ex(n, C_2k) > 0.  The constant c is a rational p / q, which is not a
restriction.  The lower bound on ex(n, C_2k) is given by a graph with m edges and no cycle of length
2k, such that m >= (p / q) n^(1 + 1/k), that is (q m)^k >= p^k n^(k+1). *)

From GraphTheory Require Import preliminaries digraph sgraph.
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

(** The cycle on [n] vertices ([3 <= n] is meant). *)
Definition cycle_graph (n : nat) : sgraph :=
  sgraph_of_rel (fun i j : 'I_n => (val i).+1 %% n == val j).

(** ** Statement *)

Definition BM_even_cycle_turan_number_lower_bound : Prop :=
  forall k : nat, 2 <= k ->
    exists p q : nat,
      [/\ 0 < p, 0 < q
        & eventually (fun n =>
            exists G : sgraph,
              [/\ #|G| = n, ~ subgraph (cycle_graph (2 * k)) G
                & p ^ k * n ^ k.+1 <= q ^ k * #|E(G)| ^ k])].
