(** * The 5-flow conjecture

Tutte; Open Problem Garden, 5_flow_conjecture.

A bridge is an edge whose deletion disconnects its two ends.  A nowhere-zero k-flow of a graph
is an orientation of its edges together with an integer function φ on the edges such that
1 <= |φ(e)| <= k-1 for every edge e and, at every vertex v, the sum of φ over the edges leaving v
equals its sum over the edges entering v.

Conjecture: every bridgeless graph has a nowhere-zero 5-flow.

Encoding.  Graphs are the finite multigraphs of GraphTheory: loops and parallel edges are
allowed.  Each edge has a reference direction, from its source to its target; the orientation is
this one, without loss of generality since φ may be negative.  Walks use the edges in either
direction.  The graph is assumed to have an edge (otherwise the conclusion is trivial). *)

From GraphTheory Require Import mgraph.
From mathcomp Require Import boot algebra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

(** Multigraphs without labels. *)
Abbreviation mgraph := (graph unit unit).

(** The list of edges [w] is a walk from [x] to [y]; the edges are used in either direction. *)
Fixpoint uwalk (G : mgraph) (x y : G) (w : seq (edge G)) {struct w} : bool :=
  match w with
  | [::] => x == y
  | e :: w' =>
      ((source e == x) && uwalk (target e) y w') ||
      ((target e == x) && uwalk (source e) y w')
  end.

(** [e] is a bridge: every walk between its ends uses it. *)
Definition mbridge (G : mgraph) (e : edge G) : Prop :=
  forall w : seq (edge G), uwalk (source e) (target e) w -> e \in w.

(** [G] has no bridge. *)
Definition bridgeless (G : mgraph) : Prop :=
  forall e : edge G, ~ mbridge e.

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

Definition OPG_nowhere_zero_5_flow_bridgeless : Prop :=
  forall G : mgraph, 0 < #|edge G| -> bridgeless G -> nowhere_zero_flow G 5.
