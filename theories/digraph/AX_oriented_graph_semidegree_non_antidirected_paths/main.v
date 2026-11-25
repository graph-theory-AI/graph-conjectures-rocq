(** * Oriented paths in oriented graphs of semidegree k/2

Penev, Taruni, Thomassé, Trujillo-Negrete, Tyomkyn, "Two-block paths in oriented graphs of large
semidegree", 2025, arXiv:2503.23191, Question 5.1 (2503.23191__00).

An oriented graph is a digraph without loops and without directed cycles of length two.  Its
minimum semidegree δ⁰(G) is the minimum of the in-degrees and out-degrees of its vertices.  An
orientation of a path is antidirected if consecutive arcs have opposite directions.

Question 5.1: is it true that every oriented graph G with δ⁰(G) >= k/2 contains every orientation
of the path with k edges, save for the antidirected orientations?  The proposition states a
positive answer.

Encoding.  Digraphs are those of GraphTheory ([diGraph]: a finite type of vertices with a boolean
relation [--]).  The path has k + 1 vertices, and its orientations are the oriented digraphs whose
underlying graph is isomorphic to it.  Such an orientation is antidirected if and only if each
vertex is a source or a sink.  "δ⁰(G) >= k/2" is stated with the integer ⌈k/2⌉ ([uphalf k]), and
G has at least one vertex, otherwise its minimum semidegree is undefined.  "Contains" refers to
subdigraphs that are not necessarily induced. *)

From GraphTheory Require Import preliminaries sgraph digraph.
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

(** The path on [n] vertices. *)
Definition path_graph (n : nat) : sgraph := sgraph_of_rel (fun i j : 'I_n => (val i).+1 == val j).

(** ** Definitions copied from GraphLib/digraph.v *)

(** [D] is oriented: it has no digon, and no loop. *)
Definition oriented (D : diGraph) : Prop :=
  forall x y : D, x -- y -> ~~ (y -- x).

(** The underlying simple graph of [D]: arcs without direction, loops ignored. *)
Definition underlying (D : diGraph) : sgraph := sgraph_of_rel (@edge_rel D).

(** [D] is an orientation of the path with [k] edges. *)
Definition oriented_path (D : diGraph) (k : nat) : Prop :=
  oriented D /\ inhabited (underlying D ≃ path_graph k.+1).

(** Out-degree. *)
Definition outdeg (D : diGraph) (v : D) : nat := #|N(v)|.

(** In-degree. *)
Definition indeg (D : diGraph) (v : D) : nat := #|[set u | u -- v]|.

(** The minimum in-degree and the minimum out-degree of [D] are at least [k]. *)
Definition min_semidegree_ge (D : diGraph) (k : nat) : Prop :=
  forall v : D, (k <= outdeg v)%N /\ (k <= indeg v)%N.

(** Each vertex is a source or a sink. *)
Definition antidirected (D : diGraph) : Prop := forall v : D, indeg v = 0 \/ outdeg v = 0.

(** [D] contains a (not necessarily induced) copy of [H]. *)
Definition subdigraph (H D : diGraph) : Prop :=
  exists f : H -> D, injective f /\ forall u v : H, u -- v -> f u -- f v.

(** ** Statement *)

(** An oriented graph G with δ⁰(G) >= k/2 contains every orientation of the path with k edges
    that is not antidirected. *)
Definition AX_oriented_graph_semidegree_non_antidirected_paths : Prop :=
  forall (k : nat) (G : diGraph),
    0 < #|G| -> oriented G -> min_semidegree_ge G (uphalf k) ->
    forall P : diGraph, oriented_path P k -> ~ antidirected P -> subdigraph P G.
