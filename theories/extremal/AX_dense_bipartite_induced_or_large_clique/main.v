(** * Minimum degree, large cliques and dense bipartite induced subgraphs

Esperet, Kang, Thomassé, "Separation choosability and dense bipartite induced subgraphs", Combin.
Probab. Comput. 28 (2019), arXiv:1802.03727, Conjecture 1.4 (1802.03727__01).

Conjecture: there are functions x2 and x3 that tend to infinity such that every graph with minimum
degree at least d contains a complete subgraph on x2(d) vertices or a bipartite induced subgraph
with minimum degree at least x3(d).

Encoding.  Graphs are finite, simple and nonempty, and so is the induced subgraph.  The functions
have natural numbers as values, which is not a restriction. *)

From GraphTheory Require Import digraph sgraph connectivity.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

(** [P n] holds for every sufficiently large [n]. *)
Definition eventually (P : nat -> Prop) : Prop :=
  exists N : nat, forall n : nat, N <= n -> P n.

(** [f] tends to infinity. *)
Definition tends_to_infinity (f : nat -> nat) : Prop :=
  forall b : nat, eventually (fun n => b <= f n).

(** Every vertex has degree at least [d] (true if [G] is empty). *)
Definition min_degree_ge (G : sgraph) (d : nat) : Prop := forall v : G, d <= #|N(v)|.

(** [G] is bipartite: it has a bipartition (a set [A] such that each edge has exactly one end in
    [A]). *)
Definition bipartite (G : diGraph) : Prop := exists A : {set G}, bipartition A.

(** ** Definitions copied from GraphLib/extremal.v *)

(** [G] has a nonempty bipartite induced subgraph of minimum degree at least [d]. *)
Definition dense_bipartite_induced (G : sgraph) (d : nat) : Prop :=
  exists S : {set G}, [/\ S != set0, bipartite (induced S) & min_degree_ge (induced S) d].

(** ** Statement *)

Definition AX_dense_bipartite_induced_or_large_clique : Prop :=
  exists x2 x3 : nat -> nat,
    [/\ tends_to_infinity x2, tends_to_infinity x3
      & forall (d : nat) (G : sgraph), 0 < #|G| -> min_degree_ge G d ->
          (exists S : {set G}, clique S /\ x2 d <= #|S|) \/
          dense_bipartite_induced G (x3 d)].
