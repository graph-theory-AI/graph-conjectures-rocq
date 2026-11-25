(** * Existence of directed Kneser graphs

Hochstättler, Schröder, Steiner, "On the complexity of digraph colourings and vertex
arboricity", DMTCS 22:1 (2020), arXiv:1812.02420, Problem 5.40 (1812.02420__03).

A digraph is acyclic if it has no directed cycle (two opposite arcs form a directed cycle of
length two).  For k >= b, a directed Kneser graph K(k,b) is a digraph whose vertices are the
b-element subsets of [k] = {1,...,k}, and such that, for all vertices B_1,...,B_l, the
subdigraph induced by {B_1,...,B_l} is acyclic if and only if B_1 ∩ ... ∩ B_l is not empty.

Problem 5.40: for given k >= b, does a directed Kneser graph K(k,b) exist?  The proposition
states a positive answer for all k and b with 1 <= b <= k.

Encoding.  Digraphs are those of GraphTheory ([diGraph]): a finite type of vertices with a
boolean relation [--].  Parallel arcs are not represented, which changes neither the directed
cycles nor the answer.  Loops are not excluded a priori, but the required property excludes
them since b >= 1.  The case b = 0 is left out: the unique vertex, the empty set, would need a
loop (and there are no loops in the paper).  The case of the empty family (l = 0) is included:
it is acyclic and, as k >= 1, its intersection, taken to be [k], is not empty. *)

From GraphTheory Require Import digraph.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/digraph.v *)

(** [D] has no directed cycle: no edge [u -- v] such that [v] reaches [u]
    (a loop or a digon is a directed cycle). *)
Definition acyclic (D : diGraph) : bool :=
  [forall u : D, forall v : D, (u -- v) ==> ~~ connect (--) v u].

(** ** Definitions specific to the conjecture *)

(** The [b]-element subsets of a [k]-element set. *)
Definition bsubset (k b : nat) : finType := {S : {set 'I_k} | #|S| == b}.

(** The digraph on the [b]-element subsets with arc relation [R]. *)
Definition kneser_digraph (k b : nat) (R : rel (bsubset k b)) : diGraph := DiGraph R.

(** The members of the family [X] of [b]-element subsets have a common element. *)
Definition common_intersection_nonempty (k b : nat) (X : {set bsubset k b}) : Prop :=
  exists i : 'I_k, forall B : bsubset k b, B \in X -> i \in val B.

(** The digraph with arc relation [R] is a directed Kneser graph: a family of vertices induces an
    acyclic subdigraph if and only if its members have a common element. *)
Definition directed_kneser_property (k b : nat) (R : rel (bsubset k b)) : Prop :=
  forall X : {set kneser_digraph R},
    acyclic (induced X) <-> common_intersection_nonempty X.

(** ** Statement *)

(** The directed Kneser graph K(k,b) exists for all k >= b >= 1. *)
Definition AX_directed_kneser_graphs_existence : Prop :=
  forall k b : nat, 0 < b -> b <= k ->
    exists R : rel (bsubset k b), directed_kneser_property R.
