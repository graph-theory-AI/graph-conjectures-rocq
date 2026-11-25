(** * Unit vector flows

Jain; Open Problem Garden, unit_vector_flows (first of the two conjectures).

A flow of a graph with values in R^3 assigns a vector to each edge so that, for a reference
direction of the edges, the vectors leaving each vertex and the vectors entering it have the same
sum.  The unit sphere S^2 is the set of vectors of R^3 of norm 1.

Conjecture: every graph without a bridge has a flow with values in S^2.

Encoding.  Graphs are finite multigraphs, with loops and parallel edges, not necessarily
connected, and with at least one edge.  The real numbers are replaced by an arbitrary real closed
field, which gives an equivalent proposition by Tarski's transfer principle.  The second conjecture
of the source, on a map from S^2 to {-4,...,4} \ {0}, is not included. *)

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

End Flows.

(** ** Definitions specific to the conjecture *)

(** [x] is a vector of norm 1, that is, a point of S^2. *)
Definition unit_vector (R : rcfType) (x : 'rV[R]_3) : bool :=
  (\sum_(i < 3) x ord0 i ^+ 2 == 1)%R.

(** ** Statement *)

Definition OPG_bridgeless_unit_vector_s2_flow : Prop :=
  forall (R : rcfType) (G : mgraph),
    0 < #|edge G| -> bridgeless G ->
    exists phi : edge G -> 'rV[R]_3, (forall e : edge G, unit_vector (phi e)) /\ conservative phi.
