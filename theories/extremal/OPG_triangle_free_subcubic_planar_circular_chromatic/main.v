(** * Circular colouring of triangle-free subcubic planar graphs

Ghebleh, Zhu; Open Problem Garden, circular_chromatic_number_of_triangle_free_planar_graphs.

A (p,q)-colouring of a graph gives to each vertex a colour in {0, ..., p-1} such that
q <= |i - j| <= p - q for the colours i and j of any two adjacent vertices.  The circular chromatic
number χ_c is the minimum of the p/q such that there is a (p,q)-colouring.

Problem: does every triangle-free planar graph of maximum degree three have circular chromatic
number at most 20/7?  The proposition states the positive answer.

Encoding.  Graphs are finite and simple, and planarity is expressed by excluded minors (Wagner's
theorem).  The maximum degree is at most 3, which is equivalent: the triangle-free graphs of maximum
degree at most 2 have χ_c <= 5/2.  "χ_c(G) = r" is a relation between G and r; there is such an r,
and it is rational, whenever G has an edge. *)

From GraphTheory Require Import preliminaries digraph sgraph minor.
From mathcomp Require Import boot order algebra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.Theory GRing.Theory Num.Theory.

(** ** Definitions copied from GraphLib/misc.v *)

(** The maximum degree of [G] (0 if [G] is empty). *)
Definition Delta (G : sgraph) : nat := \max_(x : G) #|N(x)|.

(** [G] has no triangle. *)
Definition triangle_free (G : sgraph) : Prop :=
  forall x y z : G, x -- y -> y -- z -> z -- x -> False.

(** ** Definitions copied from GraphLib/topological.v *)

(** [G] is planar: it has no minor [K_5] or [K_3,3]. *)
Definition planar (G : sgraph) : Prop :=
  ~ minor G 'K_5 /\ ~ minor G (KB 3 3).

(** ** Definitions copied from GraphLib/chromatic.v *)

(** [c] is a circular [(p,q)]-colouring: its values are less than [p] and, for adjacent
    vertices, they differ by at least [q] and at most [p - q]. *)
Definition circular_coloring (V : Type) (adj : V -> V -> bool) (p q : nat) (c : V -> nat) : Prop :=
  (forall v, (c v < p)%N) /\
  (forall u v, adj u v ->
     (q <= absz (Posz (c u) - Posz (c v))%R)%N /\
     (absz (Posz (c u) - Posz (c v))%R <= p - q)%N).

(** The circular chromatic number is [r]: the least [p / q] such that there is a circular
    [(p,q)]-colouring (there is none if no two vertices are adjacent). *)
Definition circular_chromatic_number (V : Type) (adj : V -> V -> bool) (r : rat) : Prop :=
  (exists p q : nat, (0 < q)%N /\ (exists c, circular_coloring adj p q c) /\ r = (p%:Q / q%:Q)%R) /\
  (forall p q : nat, (0 < q)%N -> (exists c, circular_coloring adj p q c) -> (r <= p%:Q / q%:Q)%R).

(** ** Statement *)

Definition OPG_triangle_free_subcubic_planar_circular_chromatic : Prop :=
  forall (G : sgraph) (r : rat),
    triangle_free G -> planar G -> Delta G <= 3 ->
    circular_chromatic_number (fun x y : G => x -- y) r -> (r <= 20%:Q / 7%:Q)%R.
