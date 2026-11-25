(** * Infinitely many graphs without finite induced-saturated graph

Bonamy, Groenland, Johnston, Morrison, Scott, "Infinite induced-saturated graphs",
arXiv:2506.08810, Problem 21 (2506.08810__00).

A graph G on at least two vertices is H-induced-saturated if it has no induced subgraph isomorphic
to H, but it has one when any edge is added or deleted.

Problem 21: is there an infinite family of finite graphs, not containing cliques or independent
sets, such that for all H in the family there is no finite H-induced-saturated graph?

The proposition states that the answer is yes.

Encoding.  Graphs are finite and simple, up to isomorphism.  A family of finite graphs is infinite
if and only if its members have an unbounded number of vertices. *)

From GraphTheory Require Import digraph sgraph dom.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

(** [G] has an induced subgraph isomorphic to [H]. *)
Definition has_induced_copy (G H : sgraph) : Prop := inhabited (H ⇀ G).

(** [G] has no induced subgraph isomorphic to [H]. *)
Definition induced_free (G H : sgraph) : Prop := ~ has_induced_copy G H.

(** ** Definitions copied from GraphLib/extremal.v *)

(** [G] is induced [H]-saturated: it has no induced subgraph isomorphic to [H], but it has one
    when any edge is added or deleted ([G] is meant to have at least two vertices). *)
Definition induced_saturated (H G : sgraph) : Prop :=
  induced_free G H /\
  (forall a b : G, a != b -> ~~ (a -- b) -> induced_free (add_edge a b) H -> False) /\
  forall e : {set G}, e \in E(G) -> induced_free (del_edges e) H -> False.

(** ** Definitions specific to the conjecture *)

(** The class [F] has infinitely many members, up to isomorphism. *)
Definition infinite_class (F : sgraph -> Prop) : Prop :=
  forall n : nat, exists H : sgraph, F H /\ n <= #|H|.

(** ** Statement *)

Definition AX_induced_saturated_no_finite_infinite_family : Prop :=
  exists F : sgraph -> Prop,
    infinite_class F /\
    forall H : sgraph, F H ->
      [/\ ~ clique [set: H], ~ stable [set: H]
        & forall G : sgraph, 1 < #|G| -> ~ induced_saturated H G].
