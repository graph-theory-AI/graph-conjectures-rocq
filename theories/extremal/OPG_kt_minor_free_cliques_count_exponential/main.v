(** * Number of cliques in graphs without K_t minor

Wood; Open Problem Garden, number_of_cliques_in_minor_closed_classes.

A clique is a set of pairwise adjacent vertices, not necessarily maximal.

Question: is there a constant c such that every graph with n vertices and without K_t minor has at
most c^t n cliques?

The proposition states the answer yes.

Encoding.  The constant c is a natural number, which is not a restriction.  The empty clique is not
counted.  This does not matter either: a graph with a vertex has a clique of one vertex, so that
counting the empty clique at most doubles the number of cliques.  The guard t > 0 is harmless, as
every graph has a K_0 minor. *)

From GraphTheory Require Import digraph sgraph coloring minor.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

(** The number of nonempty cliques of [G]. *)
Definition nonempty_clique_count (G : sgraph) : nat :=
  #|[set S in cliques [set: G] | S != set0]|.

(** ** Statement *)

Definition OPG_kt_minor_free_cliques_count_exponential : Prop :=
  exists c : nat, forall (t : nat) (G : sgraph),
    0 < t -> ~ minor G 'K_t -> nonempty_clique_count G <= c ^ t * #|G|.
