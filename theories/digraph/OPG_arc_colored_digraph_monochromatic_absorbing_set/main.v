(** * Monochromatic reachability in arc-coloured digraphs

Sands, Sauer, Woodrow, "On monochromatic paths in edge-coloured digraphs", J. Combin. Theory Ser. B
33 (1982); Open Problem Garden, monochromatoc_reachability_in_arc_colored_digraphs.

In an arc-coloured digraph, a directed path is monochromatic if all its arcs have the same colour.
A set of vertices is stable if there is no arc between its vertices.

Conjecture: for every k, there is an integer f(k) such that every digraph D whose arcs are coloured
with k colours has a set S of vertices that is the union of f(k) stable sets, such that every vertex
has a monochromatic directed path to some vertex of S.

Encoding.  Digraphs are those of GraphTheory ([diGraph]): a finite type of vertices with a boolean
relation [--].  They have no loop here (a vertex with a loop is in no stable set), but digons are
allowed.  A colouring is a function [c] on all couples of vertices, whose values matter only on the
arcs.  The stable sets are [A i] for [i : 'I_f], where [f] is f(k).  A path may have length 0, and
its colour may depend on the vertex. *)

From GraphTheory Require Import digraph.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/digraph.v *)

(** There is a monochromatic directed path from [v] to [w], for the arc-colouring [c]
    ([c] matters only on arcs). *)
Definition mono_reach (D : diGraph) (C : finType) (c : D -> D -> C) (v w : D) : bool :=
  [exists i : C, connect (fun x y : D => (x -- y) && (c x y == i)) v w].

(** There is no arc inside [S]. *)
Definition arc_free (D : diGraph) (S : {set D}) : bool :=
  [forall u in S, [forall v in S, ~~ (u -- v)]].

(** ** Statement *)

Definition OPG_arc_colored_digraph_monochromatic_absorbing_set : Prop :=
  forall k : nat, exists f : nat,
    forall (D : diGraph) (c : D -> D -> 'I_k), irreflexive (@edge_rel D) ->
      exists A : 'I_f -> {set D},
        (forall i : 'I_f, arc_free (A i)) /\
        (forall v : D, exists2 s : D, s \in \bigcup_(i < f) A i & mono_reach c v s).
