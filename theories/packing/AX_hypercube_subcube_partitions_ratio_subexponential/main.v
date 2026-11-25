(** * Partitions of the hypercube into subcubes of dimension at most 2

Alon, Balogh, Potapov, "Partitioning the hypercube into smaller hypercubes", arXiv:2401.00299,
Problem 1.10 (2401.00299__04).

A subcube of the hypercube {0,1}^d is a set of vertices obtained by fixing some coordinates and
letting the others vary; the number of the latter is its dimension.  Let f(d) be the number of
partitions of {0,1}^d into subcubes, f_{<=2}(d) be the number of those where all subcubes have
dimension at most 2, and n = 2^(d-1).

Problem: is the ratio f(d) / f_{<=2}(d) subexponential in n?

The proposition states that it is: for every ε > 0, f(d) / f_{<=2}(d) <= 2^(ε n) for every large
enough d.

Encoding.  It is enough to consider ε = 1/q for integers q > 0, and the inequality is then raised to
the power q and multiplied by the denominator, so that it is an inequality between integers. *)

From GraphTheory Require Import digraph sgraph.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

Section Hypercube.
Variable d : nat.

(** Tuples that differ at exactly one position. *)
Definition hypercube_rel : rel (d.-tuple bool) :=
  fun x y => #|[set i : 'I_d | tnth x i != tnth y i]| == 1.

Lemma hypercube_sym : symmetric hypercube_rel.
Proof.
move=> x y; rewrite /hypercube_rel.
suff -> : [set i : 'I_d | tnth x i != tnth y i] = [set i : 'I_d | tnth y i != tnth x i] by [].
by apply/setP => i; rewrite !inE eq_sym.
Qed.

Lemma hypercube_irrefl : irreflexive hypercube_rel.
Proof.
move=> x; rewrite /hypercube_rel.
suff -> : [set i : 'I_d | tnth x i != tnth x i] = set0 by rewrite cards0.
by apply/setP => i; rewrite !inE eqxx.
Qed.

(** The hypercube of dimension [d]. *)
Definition hypercube : sgraph := SGraph hypercube_sym hypercube_irrefl.

End Hypercube.

(** ** Definitions copied from GraphLib/packing.v *)

(** The subcube of the hypercube given by [c]: the coordinate [i] is fixed to [b] if
    [c i = Some b], and free if [c i = None]. *)
Definition subcube (d : nat) (c : {ffun 'I_d -> option bool}) : {set hypercube d} :=
  [set x : hypercube d | [forall i : 'I_d, oapp (fun b => tnth x i == b) true (c i)]].

(** The dimension of the subcube given by [c]. *)
Definition subcube_dim (d : nat) (c : {ffun 'I_d -> option bool}) : nat :=
  #|[set i : 'I_d | c i == None]|.

(** [S] is a subcube. *)
Definition is_subcube (d : nat) (S : {set hypercube d}) : bool :=
  [exists c : {ffun 'I_d -> option bool}, S == subcube c].

(** The partitions of the hypercube into subcubes. *)
Definition subcube_partitions (d : nat) : {set {set {set hypercube d}}} :=
  [set P : {set {set hypercube d}} |
     partition P [set: hypercube d] && [forall S in P, is_subcube S]].

(** ** Definitions specific to the conjecture *)

(** [S] is a subcube of dimension at most [k]. *)
Definition is_subcube_dim_le (d k : nat) (S : {set hypercube d}) : bool :=
  [exists c : {ffun 'I_d -> option bool}, (S == subcube c) && (subcube_dim c <= k)].

(** The partitions of the hypercube into subcubes of dimension at most [k]. *)
Definition subcube_partitions_dim_le (d k : nat) : {set {set {set hypercube d}}} :=
  [set P in subcube_partitions d | [forall S in P, @is_subcube_dim_le d k S]].

(** ** Statement *)

Definition AX_hypercube_subcube_partitions_ratio_subexponential : Prop :=
  forall q : nat,
    0 < q ->
    exists d0 : nat,
      forall d : nat, d0 <= d ->
        #|subcube_partitions d| ^ q <=
          2 ^ (2 ^ d.-1) * #|subcube_partitions_dim_le d 2| ^ q.
