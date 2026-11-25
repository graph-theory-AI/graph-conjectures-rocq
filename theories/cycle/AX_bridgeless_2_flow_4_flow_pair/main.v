(** * 1/2-flow-pairs of bridgeless graphs

Open problems of the 33rd Workshop on Cycles and Colourings (presented by Rajník),
arXiv:2511.02892, Conjecture 6.1 (2511.02892__06).

A bridge is an edge whose deletion disconnects its two ends.  A k-flow of a graph, k >= 2, is an
orientation of the edges together with an integer function φ on the edges such that |φ(e)| < k for
every edge e (0 is allowed) and, at every vertex v, the sum of φ over the edges leaving v equals its
sum over the edges entering v.

Conjecture: every bridgeless graph has a 2-flow φ_2 and a 4-flow φ_4 such that, for any edge e, if
φ_2(e) = 0 then |φ_4(e)| >= 2.  Such a pair is called a 1/2-flow-pair.

Encoding.  Graphs are the finite multigraphs of GraphTheory: loops and parallel edges are allowed.
Each edge has a reference direction, from its source to its target; the orientation is this one for
both flows, without loss of generality since the values may be negative.  Walks use the edges in
either direction.  The graph is assumed to have an edge (otherwise the conclusion is trivial). *)

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

(** [phi] is a [k]-flow (possibly with zeros). *)
Definition kflow (k : nat) (phi : edge G -> int) : Prop :=
  conservative phi /\ forall e : edge G, `|phi e| <= (k.-1)%:R.

End Flows.

(** ** Definitions specific to the conjecture *)

(** [G] has a 2-flow and a 4-flow whose absolute value is at least 2 on the edges where the 2-flow
    is zero. *)
Definition half_flow_pair (G : mgraph) : Prop :=
  (exists phi2 phi4 : edge G -> int,
    [/\ kflow 2 phi2,
        kflow 4 phi4
      & forall e : edge G, phi2 e = 0 -> 2%:R <= `|phi4 e|])%R.

(** ** Statement *)

Definition AX_bridgeless_2_flow_4_flow_pair : Prop :=
  forall G : mgraph, 0 < #|edge G| -> bridgeless G -> half_flow_pair G.
