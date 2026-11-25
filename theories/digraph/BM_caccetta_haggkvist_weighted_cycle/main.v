(** * The weighted Caccetta–Häggkvist conjecture

Bollobás, Scott; Bondy, Murty, "Graph Theory", Appendix A, problem 70.

Digraphs are strict (without loops or parallel arcs).  Given a weight function w on the arcs of a
digraph, w⁻(v) and w⁺(v) denote the total weight of the arcs entering and leaving the vertex v.  The
weight of a directed cycle is the sum of the weights of its arcs.

Conjecture: let D be a strongly connected digraph with a positive weight function w on its arcs such
that w⁻(v) >= 1 and w⁺(v) >= 1 for every vertex v.  Then D contains a directed cycle of weight at
least 1.

Encoding.  Digraphs are those of GraphTheory ([diGraph]): a finite type of vertices with a boolean
relation [--], without loop here (the conjecture fails with loops).  Digons are allowed, and are
directed cycles of length two.  D has at least one vertex.  The weight function is defined on all
couples of vertices, but only its values on arcs matter.  Weights are rational numbers, which is
equivalent to real ones: the weights of a real counterexample can be slightly increased into
rational ones.  Directed cycles are sequences of distinct vertices. *)

From GraphTheory Require Import digraph.
From mathcomp Require Import boot order algebra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/digraph.v *)

(** The vertices [c] form a directed cycle, of length [size c] (a loop or a digon is one). *)
Definition dicycle (D : diGraph) (c : seq D) : bool := ~~ nilp c && ucycleb (--) c.

(** [D] is strongly connected. *)
Definition strongly_connected (D : diGraph) : bool :=
  [forall x : D, forall y : D, connect (--) x y].

(** ** Definitions specific to the conjecture *)

(** The total weight of the arcs entering [v]. *)
Definition in_weight (D : diGraph) (w : D -> D -> rat) (v : D) : rat :=
  (\sum_(u : D | u -- v) w u v)%R.

(** The total weight of the arcs leaving [v]. *)
Definition out_weight (D : diGraph) (w : D -> D -> rat) (v : D) : rat :=
  (\sum_(u : D | v -- u) w v u)%R.

(** The weight of the directed cycle [c]: the sum of the weights of the arcs from the vertices of
    [c] to the next ones. *)
Definition dicycle_weight (D : diGraph) (w : D -> D -> rat) (c : seq D) : rat :=
  (\sum_(v <- c) w v (next c v))%R.

(** ** Statement *)

Definition BM_caccetta_haggkvist_weighted_cycle : Prop :=
  forall (D : diGraph) (w : D -> D -> rat),
    0 < #|D| -> irreflexive (@edge_rel D) -> strongly_connected D ->
    (forall u v : D, u -- v -> 0 < w u v)%R ->
    (forall v : D, 1 <= in_weight w v)%R ->
    (forall v : D, 1 <= out_weight w v)%R ->
    exists c : seq D, dicycle c /\ (1 <= dicycle_weight w c)%R.
