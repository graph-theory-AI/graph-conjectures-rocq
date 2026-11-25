(** * Graphs of large chromatic number and cycles in out-neighbourhoods of tournaments

Girão, Hendrey, Illingworth, Lehner, Michel, Savery, Steiner, "Chromatic number is not
tournament-local", 2023, arXiv:2305.15585, Conjecture 11 (2305.15585__01).

For a tournament T and a vertex v, N⁺_T(v) is the set of the out-neighbours of v.

Conjecture 11: for every graph G with sufficiently large chromatic number, and every tournament T
on the same vertex set, there exists a vertex v such that G[N⁺_T(v)] contains a cycle.

Encoding.  Graphs and digraphs are those of GraphTheory ([sgraph] and [diGraph]).  A tournament on
the same vertex set as G is given by its arc relation [r] on the vertices of G: [DiGraph r] is a
tournament.  The set N⁺_T(v) is [[set w | r v w]].  A cycle has at least three vertices. *)

From GraphTheory Require Import sgraph coloring digraph.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

Section Cycles.
Variables (T : eqType) (r : rel T).
Implicit Types c : seq T.

(** [c] is a cycle (without repetition, of length at least 3) of the relation [r]. *)
Definition seq_cycle c : bool := ucycleb r c && (2 < size c).

End Cycles.

(** ** Definitions copied from GraphLib/digraph.v *)

(** [D] is a tournament: it has no loop, and exactly one arc between any two distinct vertices. *)
Definition tournament (D : diGraph) : Prop :=
  irreflexive (@edge_rel D) /\ forall x y : D, (x != y) = (x -- y) (+) (y -- x).

(** ** Statement *)

(** If the chromatic number of G is at least C, then some out-neighbourhood of the tournament
    contains all the vertices of a cycle of G. *)
Definition AX_tournament_local_chromatic_out_neighborhood_cycle : Prop :=
  exists C : nat,
    forall (G : sgraph) (r : rel G), tournament (DiGraph r) -> C <= χ([set: G]) ->
      exists (v : G) (c : seq G), seq_cycle (--) c /\ {subset c <= [set w | r v w]}.
