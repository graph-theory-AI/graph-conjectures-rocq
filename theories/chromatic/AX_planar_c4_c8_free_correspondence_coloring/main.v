(** * Correspondence colourings of planar graphs without cycles of lengths 4 to 8

Dvořák, Postle, "Correspondence coloring and its application to list-coloring planar graphs without
cycles of lengths 4 to 8", arXiv:1508.03437, informal conjecture (1508.03437__01).

A k-correspondence assignment C for a graph G associates to each edge uv a partial matching C_uv
between {u} x [k] and {v} x [k].  A C-colouring is a map φ from the vertices to [k] such that
(u,φ(u)) and (v,φ(v)) are not matched in C_uv, for every edge uv.  The correspondence chromatic
number of G is the least k such that G is C-colourable for every k-correspondence assignment C.

Conjecture: every planar graph without cycles of lengths 4 to 8 has correspondence chromatic number
at most 3.

Encoding.  Graphs are finite and simple.  Planarity is the absence of K_5 and K_3,3 minors (Wagner's
theorem). *)

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

(** [G] has no cycle whose length is between [lo] and [hi]. *)
Definition no_cycle_length_between (G : sgraph) (lo hi : nat) : Prop :=
  forall c : seq G, seq_cycle (--) c -> lo <= size c -> size c <= hi -> False.

(** ** Definitions copied from GraphLib/chromatic.v *)

(** [G] has a colouring with [k] colours that avoids the conflicts [C]. *)
Definition conflict_colorable
    (G : sgraph) (k : nat) (C : G -> G -> 'I_k -> 'I_k -> bool) : Prop :=
  exists col : G -> 'I_k,
    forall u v : G, u -- v -> ~~ C u v (col u) (col v).

(** [C] is a correspondence assignment: for each edge, the conflicts are symmetric and form a
    matching. *)
Definition correspondence_assignment
    (G : sgraph) (k : nat) (C : G -> G -> 'I_k -> 'I_k -> bool) : Prop :=
  (forall u v : G, u -- v ->
    forall a b : 'I_k, C u v a b = C v u b a) /\
  (forall (u v : G) (a b1 b2 : 'I_k),
    u -- v -> C u v a b1 -> C u v a b2 -> b1 = b2) /\
  (forall (u v : G) (a1 a2 b : 'I_k),
    u -- v -> C u v a1 b -> C u v a2 b -> a1 = a2).

(** [G] is correspondence [k]-colourable (DP-[k]-colourable). *)
Definition correspondence_colorable (G : sgraph) (k : nat) : Prop :=
  forall C : G -> G -> 'I_k -> 'I_k -> bool,
    correspondence_assignment C -> conflict_colorable C.

(** ** Definitions copied from GraphLib/topological.v *)

(** [G] is planar: it has no minor [K_5] or [K_3,3]. *)
Definition planar (G : sgraph) : Prop :=
  ~ minor G 'K_5 /\ ~ minor G (KB 3 3).

(** ** Statement *)

Definition AX_planar_c4_c8_free_correspondence_coloring : Prop :=
  forall G : sgraph,
    planar G -> no_cycle_length_between G 4 8 -> correspondence_colorable G 3.
