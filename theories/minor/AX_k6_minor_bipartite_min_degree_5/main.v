(** * K_6 minors in bipartite graphs of minimum degree 5

Chudnovsky, Scott, Seymour, Spirkl, "Bipartite graphs with no K_6 minor", arXiv:2204.10119, open
question (2204.10119__02).

Theorem 1.6 of the source: every nonempty bipartite graph with minimum degree at least 6 has a K_6
minor.  Question: does every nonempty bipartite graph with minimum degree at least 5 have a K_6
minor?

Encoding.  Graphs are finite and simple.  The proposition states the positive answer. *)

From GraphTheory Require Import digraph sgraph connectivity minor.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

(** Every vertex has degree at least [d] (true if [G] is empty). *)
Definition min_degree_ge (G : sgraph) (d : nat) : Prop := forall v : G, d <= #|N(v)|.

(** [G] is bipartite: it has a bipartition (a set [A] such that each edge has exactly one end in
    [A]). *)
Definition bipartite (G : diGraph) : Prop := exists A : {set G}, bipartition A.

(** ** Statement *)

Definition AX_k6_minor_bipartite_min_degree_5 : Prop :=
  forall G : sgraph,
    0 < #|G| -> bipartite G -> min_degree_ge G 5 -> minor G 'K_6.
