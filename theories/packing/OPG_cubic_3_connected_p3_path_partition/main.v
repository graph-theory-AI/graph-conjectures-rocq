(** * Partition of a cubic 3-connected graph into paths of length 2

Kelmans, "On Λ-packing in 3-connected graphs", RUTCOR Research Report 23-2005, Rutgers University;
Open Problem Garden, partition_of_a_cubic_3_connected_graphs_into_paths_of_length_2.

A graph is cubic if all its degrees are 3.

Problem: does every 3-connected cubic graph on 3k vertices admit a partition into k paths of
length 2?

The proposition states the positive answer.

Encoding.  Graphs are finite and simple.  The parts are the vertex sets of the paths, which are not
necessarily induced paths. *)

From GraphTheory Require Import digraph sgraph connectivity.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

(** Every vertex has degree [d]. *)
Definition regular (G : sgraph) (d : nat) : Prop := forall v : G, #|N(v)| = d.

(** ** Definitions specific to the conjecture *)

(** [S] is the vertex set of a path of length 2 (with middle vertex [b]). *)
Definition is_P3 (G : sgraph) (S : {set G}) : Prop :=
  exists b x y : G, [/\ b -- x, b -- y, x != y & S = [set x; b; y]].

(** ** Statement *)

Definition OPG_cubic_3_connected_p3_path_partition : Prop :=
  forall (k : nat) (G : sgraph),
    regular G 3 -> 3.-connected G -> #|G| = 3 * k ->
    exists P : {set {set G}},
      [/\ partition P [set: G],
          (forall S : {set G}, S \in P -> is_P3 S)
        & #|P| = k].
