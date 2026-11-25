(** * Hoàng-Reed conjecture

Hoàng, Reed, "A note on short cycles in digraphs", Discrete Math. 66 (1987); Open Problem Garden,
hoand_reed_conjecture.

Conjecture: every digraph in which each vertex has out-degree at least k contains k directed cycles
C_1, ..., C_k such that C_j meets C_1 ∪ ... ∪ C_(j-1) in at most one vertex, for 2 <= j <= k.

Encoding.  Digraphs are those of GraphTheory ([diGraph]): a finite type of vertices with a boolean
relation [--].  Digons are allowed, and the digraph is nonempty.  Loops are allowed too, which
changes nothing: a digraph with a loop satisfies the conclusion, with k times the same loop.  In the
other digraphs, the directed cycles C_1, ..., C_k are distinct, as they have at least two
vertices. *)

From GraphTheory Require Import digraph.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/digraph.v *)

(** Out-degree. *)
Definition outdeg (D : diGraph) (v : D) : nat := #|N(v)|.

(** The minimum out-degree of [D] is at least [k]. *)
Definition min_outdeg_ge (D : diGraph) (k : nat) : Prop := forall v : D, (k <= outdeg v)%N.

(** The vertices [c] form a directed cycle, of length [size c] (a loop or a digon is one). *)
Definition dicycle (D : diGraph) (c : seq D) : bool := ~~ nilp c && ucycleb (--) c.

(** ** Statement *)

Definition OPG_hoang_reed_outdegree_nearly_disjoint_cycles : Prop :=
  forall (D : diGraph) (k : nat), 0 < #|D| -> min_outdeg_ge D k ->
    exists C : 'I_k -> seq D,
      (forall j : 'I_k, dicycle (C j)) /\
      (forall j : 'I_k, #|[set v in C j | [exists i : 'I_k, (i < j) && (v \in C i)]]| <= 1).
