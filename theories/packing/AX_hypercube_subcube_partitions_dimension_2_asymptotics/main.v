(** * Partitions of the hypercube into squares

Alon, Balogh, Potapov, "Partitioning the hypercube into smaller hypercubes", arXiv:2401.00299,
Problem 1.9 (2401.00299__02).

Q_d = {0,1}^d is the d-dimensional hypercube.  A subcube is a set of vertices obtained by fixing
some coordinates and letting the others vary; its dimension is the number of free coordinates.
The number of partitions of the vertices of Q_d into 2-dimensional subcubes is denoted by f_2(d).
Let n = 2^(d-1) and N = (d/e)^n.

Problem 1.9: determine the asymptotic behaviour of f_2(d).  The authors prove that
f_2(d) <= N^(1+o(1)), and believe that f_2(d) = N^(1+o(1)).

The proposition states that f_2(d) = N^(1+o(1)).

Encoding.  As log N = n (log d - 1) is equivalent to n log d, this means f_2(d) = d^(n (1+o(1))):
for every integer q > 0 and every sufficiently large d,
d^(n (1 - 1/q)) <= f_2(d) <= d^(n (1 + 1/q)).  The inequalities are raised to the power q. *)

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

(** ** Definitions specific to the conjecture *)

(** [S] is a subcube of dimension [k]. *)
Definition is_subcube_of_dim (d k : nat) (S : {set hypercube d}) : bool :=
  [exists c : {ffun 'I_d -> option bool}, (S == subcube c) && (subcube_dim c == k)].

(** The number f_2(d) of partitions of the hypercube into 2-dimensional subcubes. *)
Definition square_partition_count (d : nat) : nat :=
  #|[set P : {set {set hypercube d}} |
      partition P [set: hypercube d] && [forall S in P, is_subcube_of_dim 2 S]]|.

(** ** Statement *)

Definition AX_hypercube_subcube_partitions_dimension_2_asymptotics : Prop :=
  forall q : nat, 0 < q ->
    exists d0 : nat, forall d : nat, d0 <= d ->
      d ^ ((q - 1) * 2 ^ (d - 1)) <= square_partition_count d ^ q /\
      square_partition_count d ^ q <= d ^ ((q + 1) * 2 ^ (d - 1)).
