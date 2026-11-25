(** * Circular flow numbers of r-graphs

Steffen, "Edge-colorings and circular flow numbers on regular graphs", J. Graph Theory 79 (2015);
Open Problem Garden, circular_flow_numbers_of_r_graphs.

For a real r, a nowhere-zero r-flow of a graph is an orientation of its edges together with a
real function φ on the edges such that 1 <= |φ(e)| <= r-1 for every edge e and, at every vertex
v, the sum of φ over the edges leaving v equals its sum over the edges entering v.  The circular
flow number F_c(G) is the infimum of the r such that G has a nowhere-zero r-flow.  A
(2t+1)-regular graph is a (2t+1)-graph if at least 2t+1 edges leave every set of vertices of odd
size.

Conjecture: for every integer t > 1 and every (2t+1)-graph G, F_c(G) <= 2 + 2/t.

Encoding.  Graphs are the finite multigraphs of GraphTheory, with parallel edges; loops are
excluded by the condition on the cuts of single vertices.  Each edge has a reference direction,
from its source to its target; the orientation is this one, without loss of generality since φ
may be negative.  Flows have rational values, and F_c(G) <= c is expressed by a nowhere-zero
r-flow for every rational r > c, which is equivalent.  The empty graph is excluded. *)

From GraphTheory Require Import mgraph.
From mathcomp Require Import boot algebra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

(** Multigraphs without labels. *)
Abbreviation mgraph := (graph unit unit).

(** Every vertex is incident to [r] edges (a loop is counted once). *)
Definition mregular (G : mgraph) (r : nat) : Prop := forall v : G, #|edges_at v| = r.

(** The edges with exactly one end in [S]. *)
Definition mcut (G : mgraph) (S : {set G}) : {set edge G} :=
  [set e | (source e \in S) (+) (target e \in S)].

(** ** Definitions copied from GraphLib/chromatic.v *)

(** [G] is an [r]-graph: it is [r]-regular, and each odd cut has at least [r] edges. *)
Definition r_graph (G : mgraph) (r : nat) : Prop :=
  mregular G r /\ (forall X : {set G}, odd #|X| -> r <= #|mcut X|).

(** ** Definitions copied from GraphLib/cycle.v *)

Section Flows.
Variable G : mgraph.
Local Open Scope ring_scope.

(** [phi], with values in an abelian group, satisfies Kirchhoff's law: the values leaving each
    vertex and the values entering it have the same sum. *)
Definition conservative (V : zmodType) (phi : edge G -> V) : Prop :=
  forall v : G, \sum_(e | source e == v) phi e = \sum_(e | target e == v) phi e.

(** [G] has a circular nowhere-zero [r]-flow: a rational flow whose absolute values are between
    1 and [r - 1]. *)
Definition circular_flow (r : rat) : Prop :=
  exists phi : edge G -> rat,
    conservative phi /\
    (forall e : edge G, (1 <= `|phi e|)%R /\ (`|phi e| <= r - 1)%R).

(** The circular flow number of [G] (the infimum of the [r] such that [G] has a circular
    [r]-flow) is at most [c]. *)
Definition circular_flow_number_le (c : rat) : Prop :=
  forall r : rat, (c < r)%R -> circular_flow r.

End Flows.

(** ** Statement *)

Definition OPG_odd_r_graph_circular_flow_bound : Prop :=
  forall (t : nat) (G : mgraph),
    1 < t -> 0 < #|G| -> r_graph G (2 * t + 1) ->
    circular_flow_number_le G (2%:R + 2%:R / t%:R)%R.
