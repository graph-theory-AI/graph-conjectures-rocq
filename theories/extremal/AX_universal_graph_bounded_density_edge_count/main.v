(** * Universal graphs for graphs of bounded density

Alon, Dodson, Jackson, McCarty, Nenadov, Southern, "Universality for graphs with bounded density",
arXiv:2311.05500, Conjecture 1.1 (2311.05500__00).

The density of a graph H is m(H) = max e(H')/v(H') over its nonempty subgraphs H'.  H_d(n) is the
family of the graphs with n vertices and density at most d.  A graph G is universal for a family if
every graph of the family is isomorphic to a subgraph of G (not necessarily induced).

Conjecture: for every rational number d > 1, there is a constant C = C(d) such that, for every n,
there is a graph that is H_d(n)-universal and has at most C n^(2 - 1/d) edges.

Encoding.  Graphs are finite and simple.  The density d is a/b with 0 < b < a, and the inequality
e(G) <= C n^(2 - 1/d) is raised to the power a.  As C is arbitrary, it may be a natural number.
The densities of induced subgraphs suffice. *)

From GraphTheory Require Import digraph sgraph.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/extremal.v *)

(** The maximum density [m(H)] of [H] is at most [a / b]: so is the ratio of the number of
    edges to the number of vertices for all its induced subgraphs. *)
Definition max_density_le (H : sgraph) (a b : nat) : Prop :=
  forall S : {set H}, b * #|E(induced S)| <= a * #|S|.

(** ** Statement *)

Definition AX_universal_graph_bounded_density_edge_count : Prop :=
  forall a b : nat, 0 < b -> b < a ->
    exists C : nat, forall n : nat, exists G : sgraph,
      #|E(G)| ^ a <= C ^ a * n ^ (2 * a - b) /\
      forall H : sgraph, #|H| = n -> max_density_le H a b -> subgraph H G.
