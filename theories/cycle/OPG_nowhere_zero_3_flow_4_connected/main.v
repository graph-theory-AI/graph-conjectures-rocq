(** * The 3-flow conjecture

Tutte; Open Problem Garden, 3_flow_conjecture.

A graph is k-edge-connected if it remains connected whenever fewer than k edges are deleted.
A nowhere-zero k-flow of a graph is an orientation of its edges together with an integer
function φ on the edges such that 1 <= |φ(e)| <= k-1 for every edge e and, at every vertex v,
the sum of φ over the edges leaving v equals its sum over the edges entering v.

Conjecture: every 4-edge-connected graph has a nowhere-zero 3-flow.

Encoding.  Graphs are the finite multigraphs of GraphTheory: loops and parallel edges are
allowed.  Each edge has a reference direction, from its source to its target; the orientation is
this one, without loss of generality since φ may be negative.  Connectedness, which ignores the
directions, is that of the underlying simple graph ([skeleton]).  A single vertex with loops is
k-edge-connected for every k.  The graph is assumed to have an edge (otherwise the conclusion is
trivial). *)

From GraphTheory Require Import mgraph.
From GraphTheory Require Import digraph sgraph.
From GraphTheory Require skeleton.
From mathcomp Require Import boot algebra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

(** Multigraphs without labels. *)
Abbreviation mgraph := (graph unit unit).

(** [G] is [k]-edge-connected: it remains connected when fewer than [k] edges are deleted. *)
Definition medge_connected (G : mgraph) (k : nat) : Prop :=
  forall E : {set edge G}, #|E| < k -> connected [set: skeleton.skeleton (remove_edges E)].

(** ** Definitions copied from GraphLib/cycle.v *)

Section Flows.
Variable G : mgraph.
Local Open Scope ring_scope.

(** [phi], with values in an abelian group, satisfies Kirchhoff's law: the values leaving each
    vertex and the values entering it have the same sum. *)
Definition conservative (V : zmodType) (phi : edge G -> V) : Prop :=
  forall v : G, \sum_(e | source e == v) phi e = \sum_(e | target e == v) phi e.

(** The absolute values of [phi] are between 1 and [k - 1]. *)
Definition nowhere_zero_bounded (k : nat) (phi : edge G -> int) : Prop :=
  forall e : edge G, (1 <= `|phi e|)%R /\ (`|phi e| <= (k.-1)%:R)%R.

(** [G] has a nowhere-zero [k]-flow. *)
Definition nowhere_zero_flow (k : nat) : Prop :=
  exists phi : edge G -> int, conservative phi /\ nowhere_zero_bounded k phi.

End Flows.

(** ** Statement *)

Definition OPG_nowhere_zero_3_flow_4_connected : Prop :=
  forall G : mgraph, 0 < #|edge G| -> medge_connected G 4 -> nowhere_zero_flow G 3.
