(** * Hitting all maximum stable sets in P_t-free graphs

Hajebi, Li, Spirkl, "Hitting all maximum stable sets in P_5-free graphs", arXiv:2302.04986,
Conjecture 1.13 (2302.04986__01).

Graphs are finite and simple.  A hitting set of a graph G is a set of vertices that meets every
maximum stable set of G, and η(G) is the minimum size of a hitting set.  A class of graphs is
η-bounded if there is a function f such that η(G) <= f(ω(G)) for every graph G of the class.  A
graph is H-free if it has no induced subgraph isomorphic to H.  P_t is the path on t vertices.

Conjecture: for every integer t >= 6, the class of P_t-free graphs is η-bounded.

Encoding.  "η(G) <= b" is expressed by the existence of a hitting set of size at most b.  The graphs
of the class are assumed to be nonempty, as is implicit in the definition of η: the empty graph has
no hitting set, since its maximum stable set is empty. *)

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

(** [G] has an induced subgraph isomorphic to [H]. *)
Definition has_induced_copy (G H : sgraph) : Prop := inhabited (H ⇀ G).

(** [G] has no induced subgraph isomorphic to [H]. *)
Definition induced_free (G H : sgraph) : Prop := ~ has_induced_copy G H.

(** The path on [n] vertices. *)
Definition path_graph (n : nat) : sgraph := sgraph_of_rel (fun i j : 'I_n => (val i).+1 == val j).

(** ** Definitions copied from GraphLib/hypergraph.v *)

Section Hypergraph.
Variable T : finType.
Implicit Types (E : {set {set T}}) (e X : {set T}).

(** [X] is a vertex cover (transversal): it meets all edges. *)
Definition hg_cover X E : Prop :=
  forall e : {set T}, e \in E -> X :&: e != set0.

End Hypergraph.

(** ** Definitions copied from GraphLib/packing.v *)

(** The minimum size of a set of vertices that meets all maximum stable sets of [G] is at most
    [b]. *)
Definition stable_hitting_number_le (G : sgraph) (b : nat) : Prop :=
  exists X : {set G}, hg_cover X (maxstabsets [set: G]) /\ #|X| <= b.

(** The class [C] is η-bounded: on its graphs, the minimum size of a set of vertices that meets all
    maximum stable sets is bounded by a function of the clique number. *)
Definition eta_bounded (C : sgraph -> Prop) : Prop :=
  exists f : nat -> nat,
    forall G : sgraph, C G -> 0 < #|G| -> stable_hitting_number_le G (f ω(G)).

(** ** Statement *)

Definition AX_hitting_max_stable_sets_pt_free : Prop :=
  forall t : nat,
    6 <= t -> eta_bounded (fun G : sgraph => induced_free G (path_graph t)).
