(** * Maximum oriented chromatic number of planar graphs

Raspaud, Sopena, "Good and semi-strong colorings of oriented planar graphs", Inform. Process. Lett.
51 (1994); Open Problem Garden, oriented_chromatic_number_of_planar_graphs.

An oriented graph is a digraph without loop and without digon.  An oriented k-colouring of an
oriented graph is a homomorphism to a tournament of order k: a proper colouring with k colours such
that no two arcs have the pairs of colours (c_1,c_2) and (c_2,c_1).  The oriented chromatic number
is the minimum k for which there is an oriented k-colouring.

Problem: what is the maximum oriented chromatic number of an oriented planar graph?

The proposition only states the bounds that the Open Problem Garden gives with the problem: the
maximum M exists and 17 <= M <= 80 (the lower bound is due to Marshall, the upper bound to Raspaud
and Sopena).

Encoding.  The problem suggests no value for M: the proposition is a proxy, weaker than a
determination of M.  Digraphs are those of GraphTheory ([diGraph]): a finite type of vertices with a
boolean relation [--].  An oriented graph is planar if its underlying graph is.  An oriented
k-colouring gives an oriented k'-colouring for all k' >= k: M is the maximum oriented chromatic
number if all oriented planar graphs have an oriented M-colouring, and one of them has no oriented
(M-1)-colouring. *)

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

(** ** Definitions copied from GraphLib/homomorphism.v *)

(** There is a homomorphism from [G] to [H]. *)
Definition homs_to (G H : diGraph) : Prop := exists f : G -> H, is_dhom f.

(** ** Definitions copied from GraphLib/digraph.v *)

(** [D] is oriented: it has no digon, and no loop. *)
Definition oriented (D : diGraph) : Prop :=
  forall x y : D, x -- y -> ~~ (y -- x).

(** [D] is a tournament: it has no loop, and exactly one arc between any two distinct vertices. *)
Definition tournament (D : diGraph) : Prop :=
  irreflexive (@edge_rel D) /\ forall x y : D, (x != y) = (x -- y) (+) (y -- x).

(** The underlying simple graph of [D]: arcs without direction, loops ignored. *)
Definition underlying (D : diGraph) : sgraph := sgraph_of_rel (@edge_rel D).

(** [D] has an oriented [k]-colouring: a homomorphism to a tournament on [k] vertices. *)
Definition oriented_colorable (D : diGraph) (k : nat) : Prop :=
  exists T : diGraph, [/\ tournament T, #|T| = k & homs_to D T].

(** ** Definitions copied from GraphLib/topological.v *)

(** [G] is planar: it has no minor [K_5] or [K_3,3]. *)
Definition planar (G : sgraph) : Prop :=
  ~ minor G 'K_5 /\ ~ minor G (KB 3 3).

(** ** Statement *)

Definition proxy_OPG_planar_oriented_chromatic_number_max : Prop :=
  exists M : nat,
    [/\ 17 <= M <= 80,
        forall D : diGraph, oriented D -> planar (underlying D) -> oriented_colorable D M &
        exists D : diGraph,
          [/\ oriented D, planar (underlying D) & ~ oriented_colorable D M.-1]].
