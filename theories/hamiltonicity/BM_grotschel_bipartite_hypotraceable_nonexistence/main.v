(** * Bipartite hypotraceable graphs

Grötschel; Bondy, Murty, "Graph Theory", Appendix A, problem 91.

A graph is hypotraceable if it has no Hamilton path but every vertex-deleted subgraph has one.

Conjecture: there is no bipartite hypotraceable graph.

Encoding.  Graphs are finite and simple, with at least three vertices (the graph with two vertices
and no edge is bipartite, and it is hypotraceable in a trivial way).  Paths are sequences of
vertices. *)

From GraphTheory Require Import digraph sgraph connectivity.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

(** [G] is bipartite: it has a bipartition (a set [A] such that each edge has exactly one end in
    [A]). *)
Definition bipartite (G : diGraph) : Prop := exists A : {set G}, bipartition A.

(** ** Definitions copied from GraphLib/hamiltonicity.v *)

(** [s] is a Hamiltonian path of [G]. *)
Definition hamiltonian_path (G : sgraph) (s : seq G) : bool :=
  [&& sorted (--) s, uniq s & size s == #|G|].
Arguments hamiltonian_path : clear implicits.

(** [G] is traceable: it has a Hamiltonian path. *)
Definition traceable (G : sgraph) : Prop :=
  exists s : seq G, hamiltonian_path G s.

(** [G] is hypotraceable: it is not traceable, but it is after the deletion of any vertex. *)
Definition hypotraceable (G : sgraph) : Prop :=
  ~ traceable G /\ forall v : G, traceable (induced [set~ v]).

(** ** Statement *)

Definition BM_grotschel_bipartite_hypotraceable_nonexistence : Prop :=
  forall G : sgraph, 2 < #|G| -> bipartite G -> ~ hypotraceable G.
