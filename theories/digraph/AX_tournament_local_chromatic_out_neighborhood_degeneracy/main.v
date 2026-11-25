(** * Graphs of large chromatic number and degeneracy of out-neighbourhoods of tournaments

Girão, Hendrey, Illingworth, Lehner, Michel, Savery, Steiner, "Chromatic number is not
tournament-local", 2023, arXiv:2305.15585, Question 10 (2305.15585__00).

For a tournament T and a vertex v, N⁺_T(v) is the set of the out-neighbours of v.  A graph is
k-degenerate if each of its nonempty subgraphs has a vertex of degree at most k.  Its degeneracy
is the least such k.

Question 10: does there exist, for each integer d, an integer C such that for every graph G with
χ(G) >= C and every tournament T on the same vertex set, there is a vertex v for which G[N⁺_T(v)]
has degeneracy at least d?  The proposition states a positive answer.

Encoding.  Graphs and digraphs are those of GraphTheory ([sgraph] and [diGraph]).  A tournament on
the same vertex set as G is given by its arc relation [r] on the vertices of G: [DiGraph r] is a
tournament.  The set N⁺_T(v) is [[set w | r v w]].  That the degeneracy is at least d is stated
as: if G[N⁺_T(v)] is k-degenerate, then d <= k. *)

From GraphTheory Require Import sgraph coloring digraph.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

(** The subgraph induced by [W] is [k]-degenerate: each nonempty subset [S] of [W] has a
    vertex with at most [k] neighbours in [S]. *)
Definition degenerate_on (G : sgraph) (W : {set G}) (k : nat) : Prop :=
  forall S : {set G}, S \subset W -> S != set0 -> exists x, (x \in S) /\ #|N(x) :&: S| <= k.
Arguments degenerate_on {G} W k.

(** ** Definitions copied from GraphLib/digraph.v *)

(** [D] is a tournament: it has no loop, and exactly one arc between any two distinct vertices. *)
Definition tournament (D : diGraph) : Prop :=
  irreflexive (@edge_rel D) /\ forall x y : D, (x != y) = (x -- y) (+) (y -- x).

(** ** Statement *)

(** If the chromatic number of G is at least C, then some out-neighbourhood of the tournament
    induces a subgraph of G of degeneracy at least d. *)
Definition AX_tournament_local_chromatic_out_neighborhood_degeneracy : Prop :=
  forall d : nat, exists C : nat,
    forall (G : sgraph) (r : rel G), tournament (DiGraph r) -> C <= χ([set: G]) ->
      exists v : G, forall k : nat, degenerate_on [set w | r v w] k -> d <= k.
