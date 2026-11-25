(** * A homomorphism problem for flows

DeVos; Open Problem Garden, a_homomorphism_problem_for_flows.

Let M be an abelian group and B a subset of M such that B = -B.  A B-flow of a graph assigns an
element of B to each edge so that, for a reference direction of the edges, the values leaving each
vertex and the values entering it have the same sum.  The graph Cayley(M,B) is the simple graph
with vertex set M where u and v are joined if and only if u - v ∈ B.

Conjecture: let M and M' be abelian groups, and let B ⊆ M and B' ⊆ M' satisfy B = -B and
B' = -B'.  If there is a homomorphism from Cayley(M,B) to Cayley(M',B'), then every graph with a
B-flow has a B'-flow.

Encoding.  The groups M and M' can be infinite.  Graphs with flows are finite multigraphs, with
loops and parallel edges.  It is assumed that 0 is in neither B nor B'.  If 0 ∈ B', the conclusion
is trivial (constant flow 0); if 0 ∈ B and 0 ∉ B', it can fail, since 0 plays no role in the simple
graph Cayley(M,B): for M = B = {0} and B' = ∅, the Cayley graphs have no edges, every graph has a
B-flow, and no graph with an edge has a B'-flow. *)

From GraphTheory Require Import mgraph.
From mathcomp Require Import boot algebra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

(** Multigraphs without labels. *)
Abbreviation mgraph := (graph unit unit).

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

(** [B = -B], and [0] is not in [B]. *)
Definition connection_set (M : zmodType) (B : {pred M}) : Prop :=
  (forall x : M, (- x \in B)%R = (x \in B)) /\ (0 \notin B)%R.

(** The adjacency relation of Cayley(M,B). *)
Definition cayley_adj (M : zmodType) (B : {pred M}) : rel M :=
  fun u v => (u - v \in B)%R.

(** [G] has a [B]-flow. *)
Definition has_group_flow (M : zmodType) (B : {pred M}) (G : mgraph) : Prop :=
  exists phi : edge G -> M, conservative phi /\ (forall e : edge G, phi e \in B).

(** ** Statement *)

Definition OPG_cayley_homomorphism_transfers_group_flows : Prop :=
  forall (M M' : zmodType) (B : {pred M}) (B' : {pred M'}),
    connection_set B -> connection_set B' ->
    (exists f : M -> M', {homo f : u v / cayley_adj B u v >-> cayley_adj B' u v}) ->
    forall G : mgraph, has_group_flow B G -> has_group_flow B' G.
