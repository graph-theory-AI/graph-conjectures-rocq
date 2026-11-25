(** * Simultaneous partition of hypergraphs

Kühn, Osthus, "Maximizing several cuts simultaneously", Combin. Probab. Comput. 16 (2007); Open
Problem Garden, simultaneous_partition_of_hypergraphs.

Question: let H_1 and H_2 be two r-uniform hypergraphs on the same vertex set V, with m_1 and m_2
edges.  Is there always a partition of V into r classes V_1,...,V_r such that, for i = 1 and i = 2,
at least r! m_i / r^r - o(m_i) edges of H_i meet each of the classes V_1,...,V_r?  What is stated is
the positive answer.

Encoding.  The term o(m_i) means: for every r >= 1 and every ε = a/b > 0 there is an N such that, if
m_1 and m_2 are at least N, then the number of these edges is at least r! m_i / r^r - ε m_i.  The
inequality is multiplied by b r^r.  The classes are the fibres of a map from V to {0,...,r-1}. *)

From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/hypergraph.v *)

Section Hypergraph.
Variable T : finType.
Implicit Types (E : {set {set T}}) (e : {set T}).

(** [E] is [k]-uniform: every edge has [k] vertices. *)
Definition hg_uniform E (k : nat) : Prop := forall e, e \in E -> #|e| = k.

End Hypergraph.

(** ** Definitions specific to the conjecture *)

(** [e] meets each of the [r] classes given by [part]. *)
Definition meets_all_classes (T : finType) (r : nat) (part : T -> 'I_r) (e : {set T}) : bool :=
  [forall j : 'I_r, [exists v, (v \in e) && (part v == j)]].

(** ** Statement *)

Definition OPG_two_hypergraphs_simultaneous_r_partition : Prop :=
  forall r a b : nat, 0 < r -> 0 < a -> 0 < b ->
    exists N : nat,
      forall (T : finType) (E1 E2 : {set {set T}}),
        hg_uniform E1 r -> hg_uniform E2 r -> N <= #|E1| -> N <= #|E2| ->
        exists part : T -> 'I_r,
          b * r`! * #|E1|
            <= b * r ^ r * #|[set e in E1 | meets_all_classes part e]| + a * r ^ r * #|E1| /\
          b * r`! * #|E2|
            <= b * r ^ r * #|[set e in E2 | meets_all_classes part e]| + a * r ^ r * #|E2|.
