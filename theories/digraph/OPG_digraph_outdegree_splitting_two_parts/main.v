(** * Splitting a digraph with minimum out-degree constraints

Alon, "Disjoint directed cycles", J. Combin. Theory Ser. B 68 (1996); Open Problem Garden,
splitting_a_digraph_with_minimum_outdegree_constraints.

Problem: is there, for every d, an integer f(d) such that the vertices of any digraph with minimum
out-degree at least f(d) can be partitioned into two classes so that the subdigraph induced by each
class has minimum out-degree at least d?  The proposition states a positive answer.

Encoding.  Digraphs are those of GraphTheory ([diGraph]): a finite type of vertices with a boolean
relation [--].  There are no parallel arcs (with them, the answer is negative).  Digons are allowed.
Loops are allowed too, which does not change the answer: deleting them decreases the out-degrees by
at most one.  The digraph is nonempty, and both classes are nonempty (otherwise the partition into
all vertices and no vertex would do).  A partition is given by a set of vertices and its
complement. *)

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

(** ** Statement *)

Definition OPG_digraph_outdegree_splitting_two_parts : Prop :=
  exists f : nat -> nat,
    forall (D : diGraph) (d : nat), 0 < #|D| -> min_outdeg_ge D (f d) ->
      exists A : {set D},
        [/\ A != set0, ~: A != set0,
            min_outdeg_ge (induced A) d & min_outdeg_ge (induced (~: A)) d].
