(** * Random stable roommates

Mertens, "Random stable matchings", J. Stat. Mech. (2005); Open Problem Garden,
random_stable_roommates.

An instance of the stable roommates problem on n people consists of a linear order for each person
on the n - 1 others (the preferences of this person).  A solution is a perfect matching such that no
two people prefer each other to their partners.  Let P(n) be the probability that a random instance
(uniform among all instances) has a solution.

Conjecture: P(n) = Θ(n^(-1/4)), for even n.

Encoding.  A profile gives to each person i a permutation of all the people, seen as ranks (a
smaller rank is preferred).  The rank of i himself is never used, so each instance is given by the
same number of profiles, and P(n) is the proportion of profiles that have a solution.  The
conclusion says that P(n)^4 n is between two positive constants for every large enough even n;
taking them rational is not a restriction. *)

From mathcomp Require Import boot order algebra perm.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.Theory GRing.Theory Num.Theory.

(** ** Definitions specific to the conjecture *)

(** Some perfect matching (the fixed-point-free involution [m]) is stable for the profile [pr],
    where [pr i j] is the rank of [j] for [i]. *)
Definition stable_solvable (n : nat) (pr : {ffun 'I_n -> {perm 'I_n}}) : bool :=
  [exists m : {ffun 'I_n -> 'I_n},
    [forall i, (m (m i) == i) && (m i != i)] &&
    [forall i, [forall j, (i != j) ==>
       ~~ ((pr i j < pr i (m i))%N && (pr j i < pr j (m j))%N)]]].

(** The probability that a random profile on [n] people has a stable perfect matching. *)
Definition solvable_probability (n : nat) : rat :=
  ((#|[set pr : {ffun 'I_n -> {perm 'I_n}} | stable_solvable pr]|)%:Q
    / (#|[set: {ffun 'I_n -> {perm 'I_n}}]|)%:Q)%R.

(** ** Statement *)

Definition OPG_random_stable_roommates_solution_probability : Prop :=
  exists A B : rat, (0 < A)%R /\ (A <= B)%R /\
    exists N : nat, forall n : nat, ~~ odd n -> (N <= n)%N ->
      ((A <= solvable_probability n ^+ 4 * n%:Q)%R /\
       (solvable_probability n ^+ 4 * n%:Q <= B)%R).
