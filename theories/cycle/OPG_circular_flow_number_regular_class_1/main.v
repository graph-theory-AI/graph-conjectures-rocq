(** * Circular flow number of regular class 1 graphs

Steffen, "Edge-colorings and circular flow numbers on regular graphs", J. Graph Theory 79 (2015);
Open Problem Garden, circular_flow_number_of_regular_class_1_graphs.

A nowhere-zero r-flow of a graph G is an orientation of G together with a map φ from the edges to
the real numbers such that 1 <= |φ(e)| <= r - 1 for every edge e and, at each vertex, the values
of the edges leaving it and of the edges entering it have the same sum.  The circular flow number
F_c(G) is the infimum of the numbers r such that G has a nowhere-zero r-flow.  A graph with
maximum degree k is a class 1 graph if its chromatic index is k.

Conjecture: let t >= 1 be an integer and let G be a (2t+1)-regular graph.  If G is a class 1
graph, then F_c(G) <= 2 + 2/t.

Encoding.  Graphs are finite multigraphs, not necessarily connected, with at least one vertex.
Parallel edges are allowed, but not loops, since a graph with a loop has no proper edge colouring.
Flows have rational values: "F_c(G) <= c" is expressed by the existence of a rational nowhere-zero
r-flow for every rational number r > c.  Values are given for an arbitrary reference direction of
the edges; they can be negative, so that the orientation does not matter. *)

From GraphTheory Require Import mgraph.
From GraphTheory Require Import digraph sgraph coloring.
From mathcomp Require Import boot algebra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

(** Multigraphs without labels. *)
Abbreviation mgraph := (graph unit unit).

(** [G] has no loop. *)
Definition mloopless (G : mgraph) : Prop := forall e : edge G, source e != target e.

(** The maximum number of edges incident to a vertex (a loop is counted once). *)
Definition mDelta (G : mgraph) : nat := \max_(v : G) #|edges_at v|.

(** Every vertex is incident to [r] edges (a loop is counted once). *)
Definition mregular (G : mgraph) (r : nat) : Prop := forall v : G, #|edges_at v| = r.

(** Distinct edges with a common end. *)
Definition mline_rel (G : mgraph) : rel (edge G) :=
  fun e1 e2 => (e1 != e2) && [exists v : G, incident v e1 && incident v e2].

Lemma mline_rel_sym (G : mgraph) : symmetric (@mline_rel G).
Proof.
move=> e1 e2; rewrite /mline_rel eq_sym; congr (_ && _).
by apply/existsP/existsP=> -[v Hv]; exists v; rewrite andbC.
Qed.

Lemma mline_rel_irrefl (G : mgraph) : irreflexive (@mline_rel G).
Proof. by move=> e; rewrite /mline_rel eqxx. Qed.

(** The line graph of the multigraph [G] (parallel edges are adjacent). *)
Definition mline_graph (G : mgraph) : sgraph := SGraph (@mline_rel_sym G) (@mline_rel_irrefl G).

(** ** Definitions copied from GraphLib/chromatic.v *)

(** The chromatic index of [G] ([0] for [G] without edges; loops are allowed). *)
Definition mchromatic_index (G : mgraph) : nat := χ([set: mline_graph G]).

(** ** Definitions copied from GraphLib/cycle.v *)

(** [G] is of class 1: its chromatic index is equal to its maximum degree ([G] has no loop). *)
Definition class_one (G : mgraph) : Prop := mchromatic_index G = mDelta G.

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

Definition OPG_circular_flow_number_regular_class_1 : Prop :=
  forall (t : nat) (G : mgraph),
    1 <= t -> 0 < #|G| -> mloopless G ->
    mregular G (2 * t + 1) -> class_one G ->
    circular_flow_number_le G (2%:R + 2%:R / t%:R)%R.
