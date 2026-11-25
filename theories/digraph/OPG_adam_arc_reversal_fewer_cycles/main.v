(** * Ádám's conjecture

Ádám, "Problem 2", in Theory of Graphs and its Applications (M. Fiedler, ed.), 1964;
Open Problem Garden, adams_conjecture.

The reversal of an arc (u,v) of a digraph replaces it by (v,u).

Conjecture: every digraph with at least one directed cycle has an arc whose reversal reduces
the number of directed cycles.

Encoding.  Digraphs are those of GraphTheory ([diGraph]): a finite type of vertices with a
boolean relation [--], assumed irreflexive (no loop).  Parallel arcs are not represented: the
conjecture is about simple digraphs.  Digons (pairs of opposite arcs) are allowed, and they are
directed cycles.  The reversal of an arc of a digon amounts to its deletion, as no parallel arc
is created.  Hence a digraph with a digon trivially satisfies the conclusion, and the
proposition is equivalent to its restriction to digraphs without digon.  Directed cycles are
counted by their arc sets, so that the starting vertex does not matter. *)

From GraphTheory Require Import digraph.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/digraph.v *)

(** Reversal of the arc [a]. *)
Definition reverse_arc (D : diGraph) (a : D * D) : diGraph :=
  DiGraph (fun u v : D => if (u == a.1) && (v == a.2) then false
                          else if (u == a.2) && (v == a.1) then true else u -- v).

(** The vertices [c] form a directed cycle, of length [size c] (a loop or a digon is one). *)
Definition dicycle (D : diGraph) (c : seq D) : bool := ~~ nilp c && ucycleb (--) c.

(** The arcs of the directed cycle [c]. *)
Definition dicycle_arcs (D : diGraph) (c : seq D) : {set D * D} :=
  [set p : D * D | (p.1 \in c) && (next c p.1 == p.2)].

(** The number of directed cycles of [D], given by their sets of arcs (they have at most [#|D|]
    vertices). *)
Definition dicycle_count (D : diGraph) : nat :=
  #|[set A : {set D * D} | [exists k : 'I_#|D|.+1, exists c : k.-tuple D,
       dicycle c && (A == dicycle_arcs c)]]|.

(** ** Statement *)

Definition OPG_adam_arc_reversal_fewer_cycles : Prop :=
  forall D : diGraph, irreflexive (@edge_rel D) ->
    (exists c : seq D, dicycle c) ->
    exists a : D * D, a.1 -- a.2 /\ dicycle_count (reverse_arc a) < dicycle_count D.
