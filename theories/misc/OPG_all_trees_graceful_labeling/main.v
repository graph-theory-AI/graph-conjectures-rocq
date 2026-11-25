(** * Graceful Tree Conjecture

Kotzig, Ringel, Rosa; Open Problem Garden, graceful_tree_conjecture.

A graceful labelling of a graph with m edges is a labelling of the vertices with distinct
integers from 0 to m such that the labels |l(u) - l(v)| of the edges uv are exactly 1, ..., m.

Conjecture: every tree has a graceful labelling.

Encoding.  Trees have at least one vertex.  The labels of the m edges are required to be distinct
and between 1 and m, hence they are exactly 1, ..., m. *)

From GraphTheory Require Import digraph sgraph.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

Section Subdivision.
Variable G : sgraph.

(** The edges, with a fixed orientation. *)
Definition oriented_edge (p : G * G) : bool := (p.1 -- p.2) && (enum_rank p.1 < enum_rank p.2)%N.

End Subdivision.

(** The edges, with a fixed orientation. *)
Definition oriented_edges (G : sgraph) : {set G * G} :=
  [set p : G * G | oriented_edge p].

(** The difference of the labels of the ends of [p]. *)
Definition edge_label (G : sgraph) (l : G -> nat) (p : G * G) : nat :=
  (l p.1 - l p.2) + (l p.2 - l p.1).

(** [l] is a graceful labelling: distinct labels from 0 to the number [m] of edges, whose
    differences on the edges are distinct and between 1 and [m]. *)
Definition graceful_labeling (G : sgraph) (l : G -> nat) : Prop :=
  [/\ injective l,
      (forall v : G, l v <= #|E(G)|),
      (forall p : G * G, p \in oriented_edges G ->
         (1 <= edge_label l p) && (edge_label l p <= #|E(G)|)) &
      {in oriented_edges G &, injective (edge_label l)}].

(** ** Statement *)

Definition OPG_all_trees_graceful_labeling : Prop :=
  forall G : sgraph, 0 < #|G| -> is_tree [set: G] -> exists l : G -> nat, graceful_labeling l.
