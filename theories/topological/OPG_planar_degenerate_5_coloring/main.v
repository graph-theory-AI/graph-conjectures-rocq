(** * Degenerate colourings of planar graphs

Borodin, "A proof of B. Grünbaum's conjecture on the acyclic 5-colorability of planar graphs", Dokl.
Akad. Nauk SSSR 231, 1976; Open Problem Garden, degenerate_colorings_of_planar_graphs.

A graph is k-degenerate if each of its nonempty subgraphs has a vertex of degree at most k.

Conjecture: every simple planar graph has a proper 5-colouring such that, for 1 <= k <= 4, the union
of any k colour classes induces a (k-1)-degenerate graph.

Encoding.  Graphs are finite and simple.  Planarity is the absence of minors K_5 and K_3,3 (Wagner's
theorem).  In the definition of degeneracy, it suffices to consider induced subgraphs.  Colour
classes may be empty. *)

From GraphTheory Require Import digraph sgraph minor.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

(** The subgraph induced by [W] is [k]-degenerate: each nonempty subset [S] of [W] has a
    vertex with at most [k] neighbours in [S]. *)
Definition degenerate_on (G : sgraph) (W : {set G}) (k : nat) : Prop :=
  forall S : {set G}, S \subset W -> S != set0 -> exists x, (x \in S) /\ #|N(x) :&: S| <= k.
Arguments degenerate_on {G} W k.

(** ** Definitions copied from GraphLib/topological.v *)

(** [G] is planar: it has no minor [K_5] or [K_3,3]. *)
Definition planar (G : sgraph) : Prop :=
  ~ minor G 'K_5 /\ ~ minor G (KB 3 3).

(** ** Statement *)

Definition OPG_planar_degenerate_5_coloring : Prop :=
  forall G : sgraph,
    planar G ->
    exists col : G -> 'I_5,
      (forall x y : G, x -- y -> col x != col y) /\
      (forall T : {set 'I_5},
         1 <= #|T| -> #|T| <= 4 -> degenerate_on [set v : G | col v \in T] (#|T| - 1)).
