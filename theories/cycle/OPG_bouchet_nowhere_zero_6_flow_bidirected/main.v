(** * Bouchet's 6-flow conjecture

Bouchet, "Nowhere-zero integral flows on a bidirected graph", JCTB 34 (1983); Open Problem Garden,
bouchets_6_flow_conjecture.

A bidirected graph is a graph where each edge has an arrowhead at each of its two ends, pointing
towards this end or away from it.  A nowhere-zero k-flow is a map φ from the edges to the integers
such that 1 <= |φ(e)| <= k - 1 for every edge e and, at each vertex v, the sum of φ over the ends
directed into v is equal to the sum of φ over the ends directed out of v.

Conjecture: every bidirected graph with a nowhere-zero k-flow for some k has a nowhere-zero
6-flow.

Encoding.  Graphs are finite multigraphs, with loops and parallel edges, not necessarily
connected, and with at least one edge.  The two arrowheads of an edge are given by two signs (units
of the ring of integers): 1 for an arrowhead directed into its end, -1 otherwise. *)

From GraphTheory Require Import mgraph.
From mathcomp Require Import boot algebra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Num.Theory.

(** ** Definitions copied from GraphLib/misc.v *)

(** Multigraphs without labels. *)
Abbreviation mgraph := (graph unit unit).

(** ** Definitions copied from GraphLib/cycle.v *)

Section Flows.
Variable G : mgraph.
Local Open Scope ring_scope.

(** The absolute values of [phi] are between 1 and [k - 1]. *)
Definition nowhere_zero_bounded (k : nat) (phi : edge G -> int) : Prop :=
  forall e : edge G, (1 <= `|phi e|)%R /\ (`|phi e| <= (k.-1)%:R)%R.

End Flows.

Section Bidirected.
Local Open Scope ring_scope.
Variable G : mgraph.
Variables ss st : edge G -> int.

(** A bidirection of [G]: signs at the ends of the edges, [ss e] at [source e] and [st e] at
    [target e]. *)
Definition bidirection : Prop :=
  forall e : edge G, ss e \is a GRing.unit /\ st e \is a GRing.unit.

(** The signed sum of the values around [v]. *)
Definition bidirected_net (phi : edge G -> int) (v : G) : int :=
  \sum_(e | source e == v) ss e * phi e + \sum_(e | target e == v) st e * phi e.

(** The bidirected graph has a nowhere-zero [k]-flow. *)
Definition nowhere_zero_biflow (k : nat) : Prop :=
  exists phi : edge G -> int,
    (forall v : G, bidirected_net phi v = 0) /\ nowhere_zero_bounded k phi.

End Bidirected.

(** ** Statement *)

Definition OPG_bouchet_nowhere_zero_6_flow_bidirected : Prop :=
  forall (G : mgraph) (ss st : edge G -> int),
    0 < #|edge G| -> bidirection ss st ->
    (exists k : nat, nowhere_zero_biflow ss st k) -> nowhere_zero_biflow ss st 6.
