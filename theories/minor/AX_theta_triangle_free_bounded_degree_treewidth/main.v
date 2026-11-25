(** * Treewidth of (theta, triangle)-free graphs of bounded degree

Pilipczuk, Sintiari, Thomassé, Trotignon, "(Theta, triangle)-free and (even hole, K_4)-free graphs.
Part 2: bounds on treewidth", arXiv:2001.01607, open question (2001.01607__01).

A theta is a graph formed by three internally disjoint induced paths of length at least 2 between
two vertices a and b, with no edges between the paths other than those at a and b.  A graph is
(theta, triangle)-free if none of its induced subgraphs is a theta or a triangle.

Question: for every fixed integer t >= 4, do (theta, triangle)-free graphs of maximum degree t have
bounded treewidth?

Encoding.  Graphs are finite and simple.  The proposition states the positive answer: there is a
function f such that, for t >= 4, all these graphs of maximum degree at most t have treewidth at
most f(t).  An induced theta of G is given by its three paths, as sequences of vertices of G. *)

From GraphTheory Require Import digraph sgraph treewidth.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

(** The maximum degree of [G] (0 if [G] is empty). *)
Definition Delta (G : sgraph) : nat := \max_(x : G) #|N(x)|.

Section Sequences.
Variable T : finType.
Implicit Types (s : seq T) (x y : T).

(** The elements of [s] other than [x] and [y]. *)
Definition seq_interior x y s : {set T} := [set:: s] :\: [set x; y].

(** The list of the pairs of consecutive elements of [s]: the edges of a walk. *)
Definition seq_edge_list s : seq {set T} :=
  map (fun e : T * T => [set e.1; e.2]) (zip s (behead s)).

End Sequences.

Section InducedPathsCycles.
Variable G : sgraph.
Implicit Types (p : seq G) (a b u v : G).

(** [p] is an induced path (possibly empty): adjacent vertices of [p] are consecutive. *)
Definition chordless_path p : Prop :=
  [/\ uniq p, sorted (--) p
    & forall u v : G, u \in p -> v \in p -> u -- v -> [set u; v] \in seq_edge_list p].

(** [p] is an induced path from [a] to [b]. *)
Definition chordless_path_between a b p : Prop :=
  [/\ chordless_path p, ohead p = Some a & last a p = b].

End InducedPathsCycles.

(** [G] has no triangle. *)
Definition triangle_free (G : sgraph) : Prop :=
  forall x y z : G, x -- y -> y -- z -> z -- x -> False.

(** ** Definitions copied from GraphLib/minor.v *)

(** The treewidth of [G] is at most [k] (the width of a decomposition is, in GraphTheory, the
    maximum size of a bag). *)
Definition treewidth_le (G : sgraph) (k : nat) : Prop :=
  exists (T : forest) (D : T -> {set G}), sdecomp T G D /\ width D <= k.+1.

(** ** Definitions specific to the conjecture *)

Section Theta.
Variable G : sgraph.
Implicit Types (a b : G) (p q : seq G).

(** [p] is an induced path from [a] to [b] of length at least 2. *)
Definition long_induced_path_between a b p : Prop :=
  3 <= size p /\ chordless_path_between a b p.

(** No edge joins an internal vertex of [p] to an internal vertex of [q]. *)
Definition no_cross_edges a b p q : Prop :=
  forall u v : G, u \in seq_interior a b p -> v \in seq_interior a b q -> ~~ (u -- v).

(** [G] has an induced subgraph that is a theta. *)
Definition has_induced_theta : Prop :=
  exists (a b : G) (p1 p2 p3 : seq G),
    a != b /\
    long_induced_path_between a b p1 /\
    long_induced_path_between a b p2 /\
    long_induced_path_between a b p3 /\
    [disjoint seq_interior a b p1 & seq_interior a b p2] /\
    [disjoint seq_interior a b p1 & seq_interior a b p3] /\
    [disjoint seq_interior a b p2 & seq_interior a b p3] /\
    no_cross_edges a b p1 p2 /\
    no_cross_edges a b p1 p3 /\
    no_cross_edges a b p2 p3.

End Theta.

(** ** Statement *)

Definition AX_theta_triangle_free_bounded_degree_treewidth : Prop :=
  exists f : nat -> nat,
    forall (t : nat) (G : sgraph),
      4 <= t -> Delta G <= t -> triangle_free G -> ~ has_induced_theta G ->
      treewidth_le G (f t).
