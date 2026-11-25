(** * Universal point sets for planar graphs

Mohar; Open Problem Garden, small_universal_point_sets_for_planar_graphs.

A set P of points of the plane is n-universal if every planar graph on n vertices has a drawing
where the vertices are distinct points of P and the edges are non-crossing straight line segments.

Question: is there an n-universal set of size O(n)?

The proposition states the positive answer: there is a constant c such that, for every n, there is
an n-universal set of at most cn points.

Encoding.  Graphs are finite and simple.  Planarity is the absence of minors K_5 and K_3,3
(Wagner's theorem).  The coordinates are in an arbitrary real closed field R.  This is equivalent to
the case of real numbers: for given c and n, the existence of P is a first-order property of ordered
fields, so that it has the same truth value in all real closed fields.  Edges are non-crossing if
no vertex is on an edge that is not incident to it and if edges without common end have no common
point. *)

From GraphTheory Require Import digraph sgraph minor.
From mathcomp Require Import boot order algebra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/topological.v *)

(** [G] is planar: it has no minor [K_5] or [K_3,3]. *)
Definition planar (G : sgraph) : Prop :=
  ~ minor G 'K_5 /\ ~ minor G (KB 3 3).

Section StraightLine.
Variable R : realFieldType.
Local Open Scope ring_scope.

(** The points of the plane. *)
Definition plane_point := (R * R)%type.

(** Twice the signed area of the triangle [a b c]. *)
Definition signed_area (a b c : plane_point) : R :=
  (b.1 - a.1) * (c.2 - a.2) - (b.2 - a.2) * (c.1 - a.1).

(** [a], [b] and [c] are on a line. *)
Definition collinear (a b c : plane_point) : Prop := signed_area a b c = 0.

(** [c] is on the segment [a b]. *)
Definition on_segment (a b c : plane_point) : Prop :=
  collinear a b c /\ (c.1 - a.1) * (c.1 - b.1) <= 0 /\ (c.2 - a.2) * (c.2 - b.2) <= 0.

(** The segments [a b] and [c d] are not on a line and cross at an interior point of both. *)
Definition segments_cross (a b c d : plane_point) : Prop :=
  ~ (0 < signed_area a b c * signed_area a b d) /\
  ~ (0 < signed_area c d a * signed_area c d b) /\
  signed_area a b c != 0 /\ signed_area a b d != 0 /\
  signed_area c d a != 0 /\ signed_area c d b != 0.

(** The segments [a b] and [c d] have a common point. *)
Definition segments_meet (a b c d : plane_point) : Prop :=
  segments_cross a b c d \/
  on_segment a b c \/ on_segment a b d \/ on_segment c d a \/ on_segment c d b.

(** [pos] is a planar straight-line drawing of [G]. *)
Definition straightline_planar (G : sgraph) (pos : G -> plane_point) : Prop :=
  [/\ injective pos,
      (forall w x y : G, x -- y -> w != x -> w != y -> ~ on_segment (pos x) (pos y) (pos w)) &
      (forall x y u v : G, x -- y -> u -- v -> [disjoint [set x; y] & [set u; v]] ->
         ~ segments_meet (pos x) (pos y) (pos u) (pos v)) ].

(** Every planar graph on [n] vertices has a planar straight-line drawing on points of [P]. *)
Definition universal_point_set (P : seq plane_point) (n : nat) : Prop :=
  forall G : sgraph, planar G -> #|G| = n ->
    exists pos : G -> plane_point, straightline_planar pos /\ (forall x : G, pos x \in P).

End StraightLine.

(** ** Statement *)

Definition OPG_planar_universal_point_set_linear : Prop :=
  forall R : rcfType,
    exists c : nat, forall n : nat,
      exists P : seq (plane_point R), size P <= c * n /\ universal_point_set P n.
