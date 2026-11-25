(** * Graph-codes for graphs with an even number of edges

Alon, "Graph-codes", arXiv:2301.13305, Question 1.1 (2301.13305__00).

For a fixed graph H, an H-code is a family of graphs on the vertex set {1, ..., n} such that the
symmetric difference of two distinct members (the graph of the edges that are in exactly one of
them) is never a copy of H, that is, H plus isolated vertices.  Let d_H(n) be the maximum size of an
H-code divided by 2^C(n,2), the number of graphs on {1, ..., n}.  For a family of graphs closed
under isomorphism, the codes and their density are defined likewise.

Question: is it true that the density for a family tends to 0 as n tends to infinity if and only if
the family contains a graph with an even number of edges?  Equivalently, is it true that d_H(n)
tends to 0 for every fixed graph H with an even number of edges?

The proposition states the second form, with the answer yes.

Encoding.  Graphs are finite and simple.  The graph H has at least one edge, as in the source: if H
has no edge, then every family is an H-code.  A graph on {1, ..., n} is given by its set of edges, a
subset of E(K_n).  The limit is 0 when, for every q >= 1, the inequality q |F| <= 2^C(n,2) holds for
every H-code F, for n large enough. *)

From GraphTheory Require Import digraph sgraph.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

(** [A] is the edge set of a copy of [T] in [G] (as a subgraph). *)
Definition embedded_edge_copy (G T : sgraph) (A : {set {set G}}) : Prop :=
  exists f : T -> G,
    [/\ injective f,
        (forall x y : T, x -- y -> f x -- f y)
      & A = [set f @: (e : {set T}) | e in E(T)]].
Arguments embedded_edge_copy {G} T A.

(** ** Definitions copied from GraphLib/extremal.v *)

(** [F] is an [H]-code: a set of edge sets of graphs on [0, ..., n-1] such that the symmetric
    difference of two distinct members is never the edge set of a copy of [H]. *)
Definition graph_code (n : nat) (H : sgraph) (F : {set {set {set 'K_n}}}) : Prop :=
  (forall A, A \in F -> A \subset E('K_n)) /\
  forall A B, A \in F -> B \in F -> A != B ->
    ~ embedded_edge_copy H ((A :\: B) :|: (B :\: A)).

(** ** Statement *)

Definition AX_graph_codes_even_edges_density_vanishes : Prop :=
  forall H : sgraph, 0 < #|E(H)| -> ~~ odd #|E(H)| ->
    forall q : nat, 1 <= q -> exists N : nat, forall n : nat, N <= n ->
      forall F : {set {set {set 'K_n}}}, graph_code H F -> q * #|F| <= 2 ^ 'C(n, 2).
