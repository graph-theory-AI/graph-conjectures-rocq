(** * List colourings of planar graphs of girth five with two precoloured cycles

Dvořák, Král', Thomas, "Three-coloring triangle-free graphs on surfaces II. 4-critical graphs in a
disk", arXiv:1302.2158, Conjecture 1.7 (1302.2158__00).

Conjecture 1.7: for every integer k >= 5, there is an integer K with the following property.  Let G
be a planar graph of girth at least five, let C1 and C2 be two cycles of G of lengths at most k, and
for every vertex v let L(v) be a set such that |L(v)| = 1 if v is in C1 or C2, and |L(v)| >= 3
otherwise.  If G has no proper colouring from the lists L, then G has a subgraph H on at most K
vertices such that C1 and C2 are subgraphs of H and H has no proper colouring from the lists L.

Encoding.  Graphs are finite and simple.  Planarity is the absence of K_5 and K_3,3 minors (Wagner's
theorem).  The girth is at least five if no cycle has length 3 or 4.  Cycles are sequences of
vertices.  The subgraph H is induced by a set S of vertices, which is equivalent: adding edges to H
removes colourings. *)

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

(** The girth of [G] is at least [g] (true if [G] is a forest). *)
Definition girth_ge (G : sgraph) (g : nat) : Prop :=
  forall c : seq G, seq_cycle (--) c -> g <= size c.

(** ** Definitions copied from GraphLib/chromatic.v *)

(** [f] is a proper colouring from the lists [L]. *)
Definition proper_list_coloring
    (G : sgraph) (C : finType) (L : G -> {set C}) (f : G -> C) : Prop :=
  (forall v : G, f v \in L v) /\
  (forall x y : G, x -- y -> f x != f y).

(** [G] has a proper colouring from the lists [L]. *)
Definition list_colorable (G : sgraph) (C : finType) (L : G -> {set C}) : Prop :=
  exists f : G -> C, proper_list_coloring L f.

(** ** Definitions copied from GraphLib/topological.v *)

(** [G] is planar: it has no minor [K_5] or [K_3,3]. *)
Definition planar (G : sgraph) : Prop :=
  ~ minor G 'K_5 /\ ~ minor G (KB 3 3).

(** ** Definitions specific to the conjecture *)

(** [c] is a cycle of length at most [k]. *)
Definition short_cycle (G : sgraph) (k : nat) (c : seq G) : Prop :=
  seq_cycle (--) c /\ size c <= k.

(** The vertices of [c1] and [c2] have one allowed colour, and the others at least three. *)
Definition cycle_precoloured_lists
    (G : sgraph) (C : finType) (L : G -> {set C}) (c1 c2 : seq G) : Prop :=
  forall v : G, if v \in [set:: c1] :|: [set:: c2] then #|L v| = 1 else 3 <= #|L v|.

(** The subgraph induced by [S] has a proper colouring from the lists [L]. *)
Definition list_colourable_induced
    (G : sgraph) (C : finType) (L : G -> {set C}) (S : {set G}) : Prop :=
  @list_colorable (induced S) C (fun v : induced S => L (val v)).

(** ** Statement *)

Definition AX_girth_5_planar_list_critical_bounded : Prop :=
  forall k : nat,
    5 <= k ->
    exists K : nat,
      forall (G : sgraph) (C : finType) (L : G -> {set C}) (c1 c2 : seq G),
        planar G ->
        girth_ge G 5 ->
        short_cycle k c1 ->
        short_cycle k c2 ->
        cycle_precoloured_lists L c1 c2 ->
        ~ list_colorable L ->
        exists S : {set G},
          [/\ #|S| <= K,
              [set:: c1] \subset S,
              [set:: c2] \subset S &
              ~ list_colourable_induced L S].
