(** * The 4-flow conjecture

Tutte; Open Problem Garden, 4_flow_conjecture.

A bridge is an edge whose deletion disconnects its two ends.  A graph H is a minor of G if there
are pairwise disjoint nonempty connected sets of vertices of G, one per vertex of H, such that G
has an edge between the sets of any two adjacent vertices of H.  A nowhere-zero k-flow of a graph
is an orientation of its edges together with an integer function φ on the edges such that
1 <= |φ(e)| <= k-1 for every edge e and, at every vertex v, the sum of φ over the edges leaving v
equals its sum over the edges entering v.

Conjecture: every bridgeless graph with no Petersen minor has a nowhere-zero 4-flow.

Encoding.  Graphs are the finite multigraphs of GraphTheory: loops and parallel edges are
allowed.  Each edge has a reference direction, from its source to its target; the orientation is
this one, without loss of generality since φ may be negative.  Walks use the edges in either
direction.  The Petersen graph is a simple graph, given by the list of its edges; it is a minor of
a multigraph if and only if it is a minor of the underlying simple graph ([skeleton]).  The graph
is assumed to have an edge (otherwise the conclusion is trivial). *)

From GraphTheory Require Import mgraph.
From GraphTheory Require Import preliminaries sgraph minor.
From GraphTheory Require skeleton.
From mathcomp Require Import boot algebra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

Lemma sgraph_of_rel_sym (V : finType) (r : rel V) :
  symmetric (fun x y => (x != y) && sc r x y).
Proof. by move=> x y /=; rewrite eq_sym orbC. Qed.

Lemma sgraph_of_rel_irrefl (V : finType) (r : rel V) :
  irreflexive (fun x y => (x != y) && sc r x y).
Proof. by move=> x; rewrite eqxx. Qed.

(** The graph on [V] whose edges are given by [r], up to symmetry and loops. *)
Definition sgraph_of_rel (V : finType) (r : rel V) : sgraph :=
  SGraph (@sgraph_of_rel_sym V r) (@sgraph_of_rel_irrefl V r).

(** The graph on [0, ..., n-1] whose edges are listed in [es]. *)
Definition edge_list_graph (n : nat) (es : seq (nat * nat)) : sgraph :=
  sgraph_of_rel (fun i j : 'I_n => (val i, val j) \in es).

(** The Petersen graph: the edges are those of the outer 5-cycle, the spokes and those of the
    inner pentagram. *)
Definition petersen_graph : sgraph :=
  edge_list_graph 10
    [:: (0,1); (1,2); (2,3); (3,4); (4,0);
        (0,5); (1,6); (2,7); (3,8); (4,9);
        (5,7); (7,9); (9,6); (6,8); (8,5) ]%N.

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

Definition OPG_nowhere_zero_4_flow_petersen_free : Prop :=
  forall G : mgraph,
    0 < #|edge G| -> bridgeless G -> ~ minor (skeleton.skeleton G) petersen_graph ->
    nowhere_zero_flow G 4.
