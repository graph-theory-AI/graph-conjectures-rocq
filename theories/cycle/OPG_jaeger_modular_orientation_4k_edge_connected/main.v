(** * Jaeger's modular orientation conjecture

Jaeger, "On circular flows in graphs", Finite and infinite sets (Eger, 1981), Colloq. Math. Soc.
János Bolyai 37 (1984); Open Problem Garden, jaegers_modular_orientation_conjecture.

A graph is k-edge-connected if it remains connected when fewer than k edges are deleted.

Conjecture: for every k >= 1, every 4k-edge-connected graph can be oriented so that
indegree(v) - outdegree(v) ≡ 0 (mod 2k+1) for every vertex v.

Encoding.  Graphs are finite multigraphs, with loops and parallel edges, and with at least one edge
(otherwise the conclusion is trivial).  An orientation tells, for each edge, if it keeps an
arbitrary reference direction.  Congruences are between integers. *)

From GraphTheory Require Import mgraph.
From GraphTheory Require Import digraph sgraph.
From GraphTheory Require skeleton.
From mathcomp Require Import boot algebra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Num.Theory.

(** ** Definitions copied from GraphLib/misc.v *)

(** Multigraphs without labels. *)
Abbreviation mgraph := (graph unit unit).

(** [G] is [k]-edge-connected: it remains connected when fewer than [k] edges are deleted. *)
Definition medge_connected (G : mgraph) (k : nat) : Prop :=
  forall E : {set edge G}, #|E| < k -> connected [set: skeleton.skeleton (remove_edges E)].

(** ** Definitions copied from GraphLib/cycle.v *)

(** The tail of [e]. *)
Definition orient_tail (G : mgraph) (o : edge G -> bool) (e : edge G) : G :=
  if o e then source e else target e.

(** The head of [e]. *)
Definition orient_head (G : mgraph) (o : edge G -> bool) (e : edge G) : G :=
  if o e then target e else source e.

(** The in-degree minus the out-degree of [v]. *)
Definition orient_imbalance (G : mgraph) (o : edge G -> bool) (v : G) : int :=
  ((#|[set e | orient_head o e == v]|)%:R - (#|[set e | orient_tail o e == v]|)%:R)%R.

(** ** Statement *)

Definition OPG_jaeger_modular_orientation_4k_edge_connected : Prop :=
  forall (k : nat) (G : mgraph),
    0 < #|edge G| -> 0 < k -> medge_connected G (4 * k) ->
    exists o : edge G -> bool,
      forall v : G, exists q : int, orient_imbalance o v = ((2 * k + 1)%:R * q)%R.
