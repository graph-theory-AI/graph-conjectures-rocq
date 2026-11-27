(** * Straight-line drawings and curvature

    Points of the plane are pairs of elements of an ordered field. *)

From GraphTheory Require Import preliminaries digraph sgraph.
From mathcomp Require Import boot order algebra fingroup perm.
From GC.GraphLib Require Import misc topological.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.Theory GRing.Theory Num.Theory.

(** ** Straight-line drawings *)

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

(** ** Curvature *)

Section Curvature.
Variable G : sgraph.

(** The combinatorial curvature at [v]: [1 - deg v / 2 + sum of 1 / |f|], where [f] ranges over
    the faces around [v]. *)
Definition combinatorial_curvature (E : embedding G) (v : G) : rat :=
  (1 - (#|darts_at v|)%:R / 2%:R + \sum_(d in darts_at v) 1 / (face_size E d)%:R)%R.

(** The combinatorial curvature is positive at each vertex. *)
Definition positive_curvature (E : embedding G) : Prop :=
  forall v : G, (0 < combinatorial_curvature E v)%R.

End Curvature.
