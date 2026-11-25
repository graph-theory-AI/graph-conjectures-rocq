(** * Cores of strongly regular graphs

Cameron, Kazanidis, "Cores of symmetric graphs", J. Australian Math. Soc. 85 (2008); Open Problem
Garden, cores_of_strongly_regular_graphs.

A graph is strongly regular if for some k, λ and μ it is k-regular, any two adjacent vertices have
exactly λ common neighbours, and any two distinct nonadjacent vertices have exactly μ common
neighbours.  A core is a graph all of whose endomorphisms are bijective.  The core of a finite graph
G is the core that is homomorphically equivalent to G (there are homomorphisms between them in both
directions), which is unique up to isomorphism.

Problem: does every strongly regular graph have either itself or a complete graph as a core?

The proposition states the positive answer: every strongly regular graph is a core or is
homomorphically equivalent to a complete graph.

Encoding.  Graphs are finite and simple.  Complete graphs, edgeless graphs, disjoint unions of
complete graphs of the same size and their complements are not excluded; they satisfy the
conclusion. *)

From GraphTheory Require Import digraph sgraph.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

(** The common neighbours of [u] and [v]. *)
Definition common_neigh (G : sgraph) (u v : G) : {set G} := N(u) :&: N(v).

(** Every vertex has degree [d]. *)
Definition regular (G : sgraph) (d : nat) : Prop := forall v : G, #|N(v)| = d.

(** [G] is strongly regular with parameters [k], [lam] and [mu] (complete and edgeless graphs
    are not excluded). *)
Definition strongly_regular (G : sgraph) (k lam mu : nat) : Prop :=
  [/\ regular G k,
      (forall x y : G, x -- y -> #|common_neigh x y| = lam)
    & (forall x y : G, x != y -> ~~ x -- y -> #|common_neigh x y| = mu)].

(** ** Definitions copied from GraphLib/homomorphism.v *)

(** There is a homomorphism from [G] to [H]. *)
Definition homs_to (G H : diGraph) : Prop := exists f : G -> H, is_dhom f.

(** [G] and [H] are homomorphically equivalent. *)
Definition hom_equiv (G H : diGraph) : Prop := homs_to G H /\ homs_to H G.

(** [G] is a core: all its endomorphisms are bijective. *)
Definition is_core (G : diGraph) : Prop := forall f : G -> G, is_dhom f -> bijective f.

(** ** Statement *)

Definition OPG_strongly_regular_core_complete_or_self : Prop :=
  forall (G : sgraph) (k lam mu : nat),
    strongly_regular G k lam mu -> is_core G \/ exists n : nat, hom_equiv G 'K_n.
