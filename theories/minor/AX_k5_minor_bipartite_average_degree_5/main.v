(** * K_5 minors in bipartite graphs of average degree 5

Chudnovsky, Scott, Seymour, Spirkl, "Bipartite graphs with no K_6 minor", arXiv:2204.10119,
informal conjecture (2204.10119__03).

Conjecture: every nonempty bipartite graph with average degree at least 5 and maximum degree at
most 6 has a K_5 minor.  (The authors only suggest that this may be true.)

Encoding.  Graphs are finite and simple.  "Nonempty" is implicit in the source: the empty graph
has no average degree.  "Average degree at least 5" is written 5 |V(G)| <= Σ_v d(v). *)

From GraphTheory Require Import digraph sgraph connectivity minor.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

(** The maximum degree of [G] (0 if [G] is empty). *)
Definition Delta (G : sgraph) : nat := \max_(x : G) #|N(x)|.

(** The average degree of [G] is at least [a / b]. *)
Definition average_degree_ge (G : sgraph) (a b : nat) : Prop :=
  a * #|G| <= b * (\sum_(v in G) #|N(v)|).

(** [G] is bipartite: it has a bipartition (a set [A] such that each edge has exactly one end in
    [A]). *)
Definition bipartite (G : diGraph) : Prop := exists A : {set G}, bipartition A.

(** ** Statement *)

Definition AX_k5_minor_bipartite_average_degree_5 : Prop :=
  forall G : sgraph,
    0 < #|G| -> bipartite G -> average_degree_ge G 5 1 -> Delta G <= 6 -> minor G 'K_5.
