(** * The Earth-Moon problem

Ringel, "Färbungsprobleme auf Flächen und Graphen", Deutscher Verlag der Wissenschaften, Berlin,
1959; Open Problem Garden, earth_moon_problem.

Problem: what is the maximum number of colours needed to colour countries so that no two countries
with a common border have the same colour, when each country consists of one region on the Earth and
one region on the Moon?  In other words, what is the maximum chromatic number of a graph that is
the union of two planar graphs on the same vertex set (such a graph is called biplanar)?

The proposition states that this maximum exists and is between 9 and 12, which are the bounds given
in the Open Problem Garden.

Encoding.  The problem suggests no value for the maximum: the proposition is a proxy, weaker than a
determination of its value.  Graphs are finite and simple.  Planarity is the absence of minors K_5
and K_3,3 (Wagner's theorem).  The two planar graphs may have edges in common. *)

From GraphTheory Require Import digraph sgraph coloring minor.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/topological.v *)

(** [G] is planar: it has no minor [K_5] or [K_3,3]. *)
Definition planar (G : sgraph) : Prop :=
  ~ minor G 'K_5 /\ ~ minor G (KB 3 3).

(** [G] is the union of two planar graphs on its vertices (thickness at most 2). *)
Definition biplanar (G : sgraph) : Prop :=
  exists (e1 e2 : rel G)
         (s1 : symmetric e1) (i1 : irreflexive e1)
         (s2 : symmetric e2) (i2 : irreflexive e2),
    [/\ planar (SGraph s1 i1),
        planar (SGraph s2 i2)
      & forall x y : G, (x -- y) = e1 x y || e2 x y ].

(** ** Statement *)

Definition proxy_OPG_earth_moon_biplanar_chromatic_number : Prop :=
  exists m : nat,
    [/\ 9 <= m <= 12,
        (forall G : sgraph, biplanar G -> χ([set: G]) <= m) &
        (exists G : sgraph, biplanar G /\ χ([set: G]) = m)].
