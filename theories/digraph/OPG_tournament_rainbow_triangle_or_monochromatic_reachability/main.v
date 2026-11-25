(** * Monochromatic reachability or rainbow triangles

Sands, Sauer, Woodrow, "On monochromatic paths in edge-coloured digraphs", J. Combin. Theory Ser. B
33 (1982); Open Problem Garden, monochromatic_reachability_vs_rainbow_triangles.

A tournament is an orientation of a complete graph.  In an arc-coloured digraph, a subgraph is
rainbow if all its arcs have distinct colours, and monochromatic if all its arcs have the same
colour.

Question: let G be a tournament whose arcs are coloured with three colours.  Is it true that G must
have either a rainbow directed cycle of length three or a vertex v such that every other vertex can
be reached from v by a monochromatic directed path?

The proposition states the positive answer.

Encoding.  Tournaments are digraphs of GraphTheory ([diGraph]: a finite type of vertices with a
boolean relation [--]) satisfying the predicate [tournament].  The tournament is assumed to have a
vertex (the empty one has neither a triangle nor a vertex v).  A colouring is a function [c] on all
ordered pairs of vertices, whose values matter only on the arcs.  The colour of the path may depend
on the vertex that it reaches. *)

From GraphTheory Require Import digraph.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/digraph.v *)

(** [D] is a tournament: it has no loop, and exactly one arc between any two distinct vertices. *)
Definition tournament (D : diGraph) : Prop :=
  irreflexive (@edge_rel D) /\ forall x y : D, (x != y) = (x -- y) (+) (y -- x).

(** There is a monochromatic directed path from [v] to [w], for the arc-colouring [c]
    ([c] matters only on arcs). *)
Definition mono_reach (D : diGraph) (C : finType) (c : D -> D -> C) (v w : D) : bool :=
  [exists i : C, connect (fun x y : D => (x -- y) && (c x y == i)) v w].

(** ** Definitions specific to the conjecture *)

(** There is a directed triangle whose three arcs have distinct colours. *)
Definition rainbow_triangle (D : diGraph) (C : finType) (c : D -> D -> C) : Prop :=
  exists x y z : D, [/\ x -- y, y -- z, z -- x & uniq [:: c x y; c y z; c z x]].

(** ** Statement *)

Definition OPG_tournament_rainbow_triangle_or_monochromatic_reachability : Prop :=
  forall (T : diGraph) (c : T -> T -> 'I_3), tournament T -> 0 < #|T| ->
    rainbow_triangle c \/ exists v : T, forall w : T, mono_reach c v w.
