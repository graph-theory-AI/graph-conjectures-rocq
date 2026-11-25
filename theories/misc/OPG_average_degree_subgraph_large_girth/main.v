(** * Subgraph of large average degree and large girth

Thomassen, "Girth in graphs", J. Combin. Theory B 35 (1983); Open Problem Garden,
subgraph_of_large_average_degree_and_large_average_degree.

Conjecture: for all positive integers g and k, there exists an integer d such that every graph of
average degree at least d contains a subgraph of average degree at least k and girth greater
than g.

Encoding.  Graphs are finite and simple, subgraphs are not necessarily induced, and both graphs
are nonempty, as the average degree of an empty graph is not defined.  A forest has girth greater
than any g. *)

From GraphTheory Require Import digraph sgraph.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

(** The average degree of [G] is at least [a / b]. *)
Definition average_degree_ge (G : sgraph) (a b : nat) : Prop :=
  a * #|G| <= b * (\sum_(v in G) #|N(v)|).

Section Cycles.
Variables (T : eqType) (r : rel T).
Implicit Types c : seq T.

(** [c] is a cycle (without repetition, of length at least 3) of the relation [r]. *)
Definition seq_cycle c : bool := ucycleb r c && (2 < size c).

End Cycles.

(** The girth of [G] is at least [g] (true if [G] is a forest). *)
Definition girth_ge (G : sgraph) (g : nat) : Prop :=
  forall c : seq G, seq_cycle (--) c -> g <= size c.

(** ** Statement *)

Definition OPG_average_degree_subgraph_large_girth : Prop :=
  forall g k : nat, 0 < g -> 0 < k ->
    exists d : nat,
      forall G : sgraph, 0 < #|G| -> average_degree_ge G d 1 ->
        exists H : sgraph,
          [/\ 0 < #|H|, subgraph H G, average_degree_ge H k 1 & girth_ge H g.+1].
