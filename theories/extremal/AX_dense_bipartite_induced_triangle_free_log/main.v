(** * Dense bipartite induced subgraphs of triangle-free graphs

Esperet, Kang, Thomassé, "Separation choosability and dense bipartite induced subgraphs",
arXiv:1802.03727, Conjecture 1.5 (1802.03727__02).

Conjecture: there is a constant C > 0 such that every triangle-free graph of minimum degree at least
d contains a bipartite induced subgraph of minimum degree at least C log d.

Encoding.  Graphs are finite, simple and nonempty, and so is the induced subgraph.  The constant is
C = 1/c for a positive integer c, which is not a restriction.  The logarithm is in base 2 and
rounded down, which only changes C (d >= 2; the case d <= 1 is clear). *)

From GraphTheory Require Import digraph sgraph connectivity.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

(** Every vertex has degree at least [d] (true if [G] is empty). *)
Definition min_degree_ge (G : sgraph) (d : nat) : Prop := forall v : G, d <= #|N(v)|.

(** [G] has no triangle. *)
Definition triangle_free (G : sgraph) : Prop :=
  forall x y z : G, x -- y -> y -- z -> z -- x -> False.

(** [G] is bipartite: it has a bipartition (a set [A] such that each edge has exactly one end in
    [A]). *)
Definition bipartite (G : diGraph) : Prop := exists A : {set G}, bipartition A.

(** ** Statement *)

Definition AX_dense_bipartite_induced_triangle_free_log : Prop :=
  exists c : nat, 0 < c /\
    forall (d : nat) (G : sgraph), 0 < #|G| -> triangle_free G -> min_degree_ge G d ->
      exists S : {set G},
        [/\ S != set0, bipartite (induced S)
          & forall v : induced S, trunc_log 2 d <= c * #|N(v)|].
