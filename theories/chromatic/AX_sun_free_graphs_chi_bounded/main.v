(** * χ-boundedness of sun-free graphs

Hajebi, Spirkl, "Suns in triangle-free graphs of large chromatic number", arXiv:2506.10227, remark
after Problem 1.4 (2506.10227__00).

For t >= 4, a t-sun is obtained from a cycle of length t by adding a neighbour of degree 1 to each
vertex of the cycle.  A graph is sun-free if it has no induced t-sun for any t >= 4.  A class of
graphs is χ-bounded if, for some function f, χ(G) <= f(ω(G)) for every G in the class.

The authors say that it could be true that the class of all sun-free graphs is χ-bounded, and this
is what is stated.

Encoding.  Graphs are finite and simple. *)

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

(** The cycle on [n] vertices ([3 <= n] is meant). *)
Definition cycle_graph (n : nat) : sgraph :=
  sgraph_of_rel (fun i j : 'I_n => (val i).+1 %% n == val j).

(** ** Definitions copied from GraphLib/chromatic.v *)

(** The class [F] is chi-bounded: on its graphs, the chromatic number is bounded by a function
    of the clique number. *)
Definition chi_bounded (F : sgraph -> Prop) : Prop :=
  exists f : nat -> nat,
    forall G : sgraph, F G -> χ([set: G]) <= f (ω([set: G])).

(** ** Definitions specific to the conjecture *)

(** The [t]-sun: the vertices [(i, false)] form a cycle of length [t], and [(i, true)] is a vertex
    of degree 1 adjacent to [(i, false)] ([3 <= t] is meant). *)
Definition sun (t : nat) : sgraph :=
  sgraph_of_rel (fun x y : 'I_t * bool =>
    if x.2 || y.2 then (x.1 == y.1) && (x.2 != y.2)
    else @edge_rel (cycle_graph t) x.1 y.1).

(** ** Statement *)

Definition AX_sun_free_graphs_chi_bounded : Prop :=
  chi_bounded (fun G : sgraph => forall t : nat, 4 <= t -> induced_free G (sun t)).
