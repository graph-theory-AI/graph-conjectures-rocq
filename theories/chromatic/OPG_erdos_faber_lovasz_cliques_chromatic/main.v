(** * The Erdős-Faber-Lovász conjecture

Erdős, Faber and Lovász (1972): Erdős, "On the combinatorial problems which I would most like to
see solved", Combinatorica 1 (1981); Open Problem Garden, erdos_faber_lovasz_conjecture.

Conjecture: if a simple graph G is the union of k pairwise edge-disjoint complete graphs, each of
which has k vertices, then the chromatic number of G is k.

Encoding.  Graphs are finite.  The complete graphs are given by their vertex sets, which are
cliques of G; they are edge-disjoint when two of them have at most one common vertex. *)

From GraphTheory Require Import digraph sgraph coloring.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions specific to the conjecture *)

(** [G] is the union of [k] pairwise edge-disjoint complete graphs on [k] vertices. *)
Definition edge_disjoint_clique_union (G : sgraph) (k : nat) : Prop :=
  exists cliqs : 'I_k -> {set G},
    [/\ (forall i, #|cliqs i| = k),
        (forall i, clique (cliqs i)),
        (forall i j, i != j -> #|cliqs i :&: cliqs j| <= 1),
        (forall x : G, exists i, x \in cliqs i)
      & (forall x y : G, x -- y -> exists i, (x \in cliqs i) && (y \in cliqs i))].

(** ** Statement *)

Definition OPG_erdos_faber_lovasz_cliques_chromatic : Prop :=
  forall (k : nat) (G : sgraph),
    edge_disjoint_clique_union G k -> χ([set: G]) = k.
