(** * Matching cut and girth

Open Problem Garden, matching_cut_and_girth.

A matching cut of a graph is a partition of its vertices into two nonempty parts such that the edges
between the two parts form a matching.

Question: for every d, is there a g such that every graph with average degree smaller than d and
girth at least g has a matching cut?

The proposition states the positive answer.

Encoding.  Graphs are finite and simple, with at least two vertices: a graph with one vertex has
average degree 0 and no matching cut.  The girth of a forest is infinite.  It suffices to consider
integers d.  The average degree is smaller than d if the sum of the degrees is smaller than dn,
where n is the number of vertices. *)

From GraphTheory Require Import digraph sgraph.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

Section Cycles.
Variables (T : eqType) (r : rel T).
Implicit Types c : seq T.

(** [c] is a cycle (without repetition, of length at least 3) of the relation [r]. *)
Definition seq_cycle c : bool := ucycleb r c && (2 < size c).

End Cycles.

(** The girth of [G] is at least [g] (true if [G] is a forest). *)
Definition girth_ge (G : sgraph) (g : nat) : Prop :=
  forall c : seq G, seq_cycle (--) c -> g <= size c.

(** ** Definitions copied from GraphLib/packing.v *)

(** [G] has a matching cut: a partition of its vertices into two nonempty parts such that each
    vertex has at most one neighbour in the other part. *)
Definition matching_cut (G : sgraph) : Prop :=
  exists A : {set G},
    [/\ A != set0, A != [set: G]
      & forall v : G,
          (v \in A -> #|N(v) :&: (~: A)| <= 1) /\
          (v \notin A -> #|N(v) :&: A| <= 1)].

(** ** Statement *)

Definition OPG_matching_cut_average_degree_girth : Prop :=
  forall d : nat, exists g : nat,
    forall G : sgraph,
      1 < #|G| -> \sum_(v : G) #|N(v)| < d * #|G| -> girth_ge G g -> matching_cut G.
