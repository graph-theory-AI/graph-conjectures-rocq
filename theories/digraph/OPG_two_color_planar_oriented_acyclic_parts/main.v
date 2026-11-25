(** * The two colour conjecture

Neumann-Lara, "Vertex colourings in digraphs. Some problems", technical report, University of
Waterloo (1985); Open Problem Garden, partitioning_planar_digraphs.

Conjecture: if G is an orientation of a simple planar graph, then there is a partition of V(G) into
two sets X_1, X_2 such that the digraph induced by X_i is acyclic for i = 1, 2.

Encoding.  Digraphs are those of GraphTheory ([diGraph]: a finite type of vertices with a boolean
relation [--]).  The orientations of simple graphs are the digraphs without loop or digon
([oriented]).  Planarity of the underlying graph is defined by excluded minors (Wagner's theorem).
One of the two parts may be empty. *)

From GraphTheory Require Import preliminaries sgraph minor digraph.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

Lemma sgraph_of_rel_sym (V : finType) (r : rel V) :
  symmetric (fun x y => (x != y) && sc r x y).
Proof. by move=> x y /=; rewrite eq_sym orbC. Qed.

Lemma sgraph_of_rel_irrefl (V : finType) (r : rel V) :
  irreflexive (fun x y => (x != y) && sc r x y).
Proof. by move=> x; rewrite eqxx. Qed.

(** The graph on [V] whose edges are given by [r], up to symmetry and loops. *)
Definition sgraph_of_rel (V : finType) (r : rel V) : sgraph :=
  SGraph (@sgraph_of_rel_sym V r) (@sgraph_of_rel_irrefl V r).

(** ** Definitions copied from GraphLib/digraph.v *)

(** [D] is oriented: it has no digon, and no loop. *)
Definition oriented (D : diGraph) : Prop :=
  forall x y : D, x -- y -> ~~ (y -- x).

(** The underlying simple graph of [D]: arcs without direction, loops ignored. *)
Definition underlying (D : diGraph) : sgraph := sgraph_of_rel (@edge_rel D).

(** [D] has no directed cycle: no edge [u -- v] such that [v] reaches [u]
    (a loop or a digon is a directed cycle). *)
Definition acyclic (D : diGraph) : bool :=
  [forall u : D, forall v : D, (u -- v) ==> ~~ connect (--) v u].

(** ** Definitions copied from GraphLib/topological.v *)

(** [G] is planar: it has no minor [K_5] or [K_3,3]. *)
Definition planar (G : sgraph) : Prop :=
  ~ minor G 'K_5 /\ ~ minor G (KB 3 3).

(** ** Statement *)

Definition OPG_two_color_planar_oriented_acyclic_parts : Prop :=
  forall D : diGraph, oriented D -> planar (underlying D) ->
    exists X : {set D}, acyclic (induced X) /\ acyclic (induced (~: X)).
