(** * Jones' conjecture

Kloks, Lee, Liu, "New algorithms for k-face cover, k-feedback vertex set, and k-disjoint cycles on
plane and planar graphs", WG 2002; Open Problem Garden, jones_conjecture.

A cycle packing of a graph G is a collection of vertex-disjoint cycles, and cp(G) denotes the
maximum size of a cycle packing.  A feedback vertex set is a set X of vertices such that G - X is
acyclic, and cc(G) denotes the minimum size of a feedback vertex set.

Conjecture: for every planar graph G, cc(G) <= 2 cp(G).

Encoding.  Graphs are finite and simple (this is no restriction: loops and parallel edges can be
subdivided).  Planarity is the absence of minors K_5 and K_3,3 (Wagner's theorem).  Cycles are
sequences of at least three distinct vertices. *)

From GraphTheory Require Import digraph sgraph minor.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

Section Cycles.
Variables (T : eqType) (r : rel T).
Implicit Types c : seq T.

(** [c] is a cycle (without repetition, of length at least 3) of the relation [r]. *)
Definition seq_cycle c : bool := ucycleb r c && (2 < size c).

End Cycles.

(** ** Definitions copied from GraphLib/topological.v *)

(** [G] is planar: it has no minor [K_5] or [K_3,3]. *)
Definition planar (G : sgraph) : Prop :=
  ~ minor G 'K_5 /\ ~ minor G (KB 3 3).

(** ** Definitions copied from GraphLib/packing.v *)

(** [X] is a feedback vertex set: it meets all cycles. *)
Definition feedback_vertex_set (G : sgraph) (X : {set G}) : Prop :=
  forall c : seq G, seq_cycle (--) c -> exists2 v : G, v \in c & v \in X.

(** The minimum size of a feedback vertex set is [m]. *)
Definition feedback_vertex_number (G : sgraph) (m : nat) : Prop :=
  (exists X : {set G}, feedback_vertex_set X /\ #|X| = m) /\
  (forall X : {set G}, feedback_vertex_set X -> m <= #|X|).

(** [cs] is a list of vertex-disjoint cycles. *)
Definition cycle_packing (G : sgraph) (cs : seq (seq G)) : Prop :=
  (forall c : seq G, c \in cs -> seq_cycle (--) c) /\
  (forall v : G, count (fun c => v \in c) cs <= 1).

(** The maximum number of vertex-disjoint cycles is [m]. *)
Definition cycle_packing_number (G : sgraph) (m : nat) : Prop :=
  (exists cs : seq (seq G), cycle_packing cs /\ size cs = m) /\
  (forall cs : seq (seq G), cycle_packing cs -> size cs <= m).

(** ** Statement *)

Definition OPG_jones_planar_feedback_vertex_cycle_packing : Prop :=
  forall (G : sgraph) (cc cp : nat),
    planar G -> feedback_vertex_number G cc -> cycle_packing_number G cp ->
    cc <= 2 * cp.
