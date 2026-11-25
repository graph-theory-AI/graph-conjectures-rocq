(** * Unfriendly partitions

Cowan, Emerson, "Proportional colorings of graphs", unpublished; Open Problem Garden,
unfriendly_partitions.

A partition of the vertices of a graph is unfriendly if every vertex has at least as many
neighbours in the other classes as in its own.

Question: does every countably infinite graph have an unfriendly partition into two sets?

The proposition states the positive answer.

Encoding.  Graphs are simple, with an arbitrary type of vertices and an adjacency relation in
[Prop].  The partition is given by a function to booleans.  (If one of its classes is empty, then
the graph has no edge, and every partition is unfriendly.)  Numbers of neighbours are compared by
injections. *)

From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/infinite.v *)

(** Simple graphs, possibly infinite. *)
Record iGraph := Build_iGraph {
  ivertex : Type;
  iedge : ivertex -> ivertex -> Prop;
  iedge_sym : forall x y, iedge x y -> iedge y x;
  iedge_irrefl : forall x, ~ iedge x x }.

(** [P] is at most as large as [Q]. *)
Definition icard_le (A B : Type) (P : A -> Prop) (Q : B -> Prop) : Prop :=
  exists f : {x : A | P x} -> {y : B | Q y}, injective f.

(** [G] is countable (possibly finite). *)
Definition countable_graph (G : iGraph) : Prop :=
  exists f : ivertex G -> nat, injective f.

(** [G] is infinite. *)
Definition infinite_graph (G : iGraph) : Prop :=
  exists f : nat -> ivertex G, injective f.

(** The partition [p] is unfriendly: each vertex has at least as many neighbours in the other
    part as in its own part. *)
Definition unfriendly (G : iGraph) (p : ivertex G -> bool) : Prop :=
  forall x : ivertex G,
    icard_le (fun w => iedge x w /\ p w = p x) (fun w => iedge x w /\ p w <> p x).

(** ** Statement *)

Definition OPG_countable_graph_unfriendly_partition : Prop :=
  forall G : iGraph, countable_graph G -> infinite_graph G ->
    exists p : ivertex G -> bool, unfriendly p.
