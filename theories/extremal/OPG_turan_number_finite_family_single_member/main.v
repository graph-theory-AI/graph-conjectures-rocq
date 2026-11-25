(** * Turán number of a finite family

Erdős, Simonovits, "Compactness results in extremal graph theory", Combinatorica 2 (1982); Open
Problem Garden, turan_number_of_a_finite_family.

The Turán number ex(n,F) of a family F of graphs is the maximum number of edges of a graph with n
vertices that contains no member of F as a subgraph.

Conjecture: for every finite family F of graphs, there is a member F0 of F such that
ex(n,F0) = O(ex(n,F)).

Encoding.  Graphs are finite and simple.  The family is nonempty and, as usual in the literature,
none of its members is a forest.  Without this guard, the family formed by the path with two edges
and by two disjoint edges is a counterexample, as ex(n,F) = 1 for n >= 2 whereas both members have
linear Turán numbers.  (If F contains a forest, then the Turán number of this forest is O(n), hence
the conclusion holds unless ex(n,F) is sublinear.)  The family is indexed by 0, ..., r-1, and the
family with the single member F0 is indexed by 0. *)

From GraphTheory Require Import digraph sgraph.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/extremal.v *)

(** [G] contains no graph of the family [Fam] as a subgraph. *)
Definition family_free (G : sgraph) (k : nat) (Fam : 'I_k -> sgraph) : Prop :=
  forall i : 'I_k, ~ subgraph (Fam i) G.

(** The Turán number [ex(n, Fam)] is [m]. *)
Definition turan_number (n : nat) (k : nat) (Fam : 'I_k -> sgraph) (m : nat) : Prop :=
  (exists G : sgraph, [/\ #|G| = n, #|E(G)| = m & family_free G Fam]) /\
  (forall m' : nat,
     (exists G : sgraph, [/\ #|G| = n, #|E(G)| = m' & family_free G Fam]) ->
     (m' <= m)%N).

(** ** Statement *)

Definition OPG_turan_number_finite_family_single_member : Prop :=
  forall (r : nat) (Fam : 'I_r -> sgraph),
    0 < r -> (forall i : 'I_r, ~ is_forest [set: Fam i]) ->
    exists (i : 'I_r) (C N : nat),
      forall n m m0 : nat, N <= n ->
        turan_number n Fam m ->
        turan_number n (fun _ : 'I_1 => Fam i) m0 ->
        m0 <= C * m.
