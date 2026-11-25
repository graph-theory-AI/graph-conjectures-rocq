(** * The Gyárfás-Sumner conjecture

Gyárfás (1975), Sumner (1981); Open Problem Garden,
graphs_with_a_forbidden_induced_tree_are_chi_bounded.

A class of graphs is χ-bounded if there is a function f such that χ(G) <= f(ω(G)) for every graph G
of the class, where ω(G) is the clique number of G.

Conjecture: for every tree T, the class of graphs with no induced subgraph isomorphic to T is
χ-bounded.

Encoding.  Graphs are finite and simple. *)

From GraphTheory Require Import digraph sgraph coloring.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

(** [G] has an induced subgraph isomorphic to [H]. *)
Definition has_induced_copy (G H : sgraph) : Prop := inhabited (H ⇀ G).

(** [G] has no induced subgraph isomorphic to [H]. *)
Definition induced_free (G H : sgraph) : Prop := ~ has_induced_copy G H.

(** ** Definitions copied from GraphLib/chromatic.v *)

(** The class [F] is chi-bounded: on its graphs, the chromatic number is bounded by a function
    of the clique number. *)
Definition chi_bounded (F : sgraph -> Prop) : Prop :=
  exists f : nat -> nat,
    forall G : sgraph, F G -> χ([set: G]) <= f (ω([set: G])).

(** ** Statement *)

Definition OPG_gyarfas_sumner_forbidden_tree_chi_bounded : Prop :=
  forall T : sgraph, is_tree [set: T] -> chi_bounded (fun G : sgraph => induced_free G T).
