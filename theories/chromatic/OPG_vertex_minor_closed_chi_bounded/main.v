(** * Vertex-minor closed classes and χ-boundedness

Geelen; Open Problem Garden, vertex_minor_closed_classes_are_chi_bounded.

A class of graphs is χ-bounded if there is a function f such that χ(G) <= f(ω(G)) for every graph G
of the class, where ω(G) is the clique number of G.  A vertex-minor of a graph is a graph obtained
by a sequence of the following operations: deleting a vertex, and complementing the subgraph
induced by the neighbourhood of a vertex (local complementation).  A class is proper if it does not
contain all graphs.

Question: is every proper vertex-minor closed class of graphs χ-bounded?

The proposition states the positive answer.

Encoding.  Graphs are finite and simple.  A class of graphs is a predicate.  Vertex-minors are up to
isomorphism. *)

From GraphTheory Require Import preliminaries digraph sgraph coloring.
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

(** ** Definitions copied from GraphLib/chromatic.v *)

(** The class [F] is chi-bounded: on its graphs, the chromatic number is bounded by a function
    of the clique number. *)
Definition chi_bounded (F : sgraph -> Prop) : Prop :=
  exists f : nat -> nat,
    forall G : sgraph, F G -> χ([set: G]) <= f (ω([set: G])).

(** ** Definitions copied from GraphLib/minor.v *)

(** The local complement of [G] at [v]: the edges are complemented in the neighbourhood of [v]. *)
Definition local_complement (G : sgraph) (v : G) : sgraph :=
  sgraph_of_rel (fun x y : G => (x -- y) (+) ((x -- v) && (y -- v))).

(** [vertex_minor G H]: [H] is a vertex-minor of [G], obtained by local complementations and
    vertex deletions (up to isomorphism). *)
Inductive vertex_minor : sgraph -> sgraph -> Prop :=
| vertex_minor_refl (G : sgraph) : vertex_minor G G
| vertex_minor_lc (G H K : sgraph) (v : H) :
    vertex_minor G H -> (local_complement v ≃ K) -> vertex_minor G K
| vertex_minor_del (G H K : sgraph) (v : H) :
    vertex_minor G H -> (induced [set~ v] ≃ K) -> vertex_minor G K.

(** The class [F] is closed under vertex-minors. *)
Definition vertex_minor_closed (F : sgraph -> Prop) : Prop :=
  forall G H : sgraph, F G -> vertex_minor G H -> F H.

(** ** Definitions specific to the conjecture *)

(** The class [F] does not contain all graphs. *)
Definition proper_class (F : sgraph -> Prop) : Prop := exists G : sgraph, ~ F G.

(** ** Statement *)

Definition OPG_vertex_minor_closed_chi_bounded : Prop :=
  forall F : sgraph -> Prop, vertex_minor_closed F -> proper_class F -> chi_bounded F.
