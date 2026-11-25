(** * χ-boundedness of the oriented graphs without a given induced oriented star

Aboulker, Bang-Jensen, Bousquet, Charbit, Havet, Maffray, Zamora, "χ-bounded families of oriented
graphs", 2016, arXiv:1605.07411, Conjecture 4 (1605.07411__01).

An oriented graph is a digraph without loop and without digon.  Its chromatic number χ and its
clique number ω are those of its underlying graph.  A class of oriented graphs is χ-bounded if there
is a function f such that χ(D) <= f(ω(D)) for every D in the class.  For an oriented graph S,
Forb(S) is the class of oriented graphs with no induced subdigraph isomorphic to S.  An oriented
star is an orientation of a star K_{1,n}.

Conjecture: for every oriented star S, Forb(S) is χ-bounded.

Encoding.  Digraphs are those of GraphTheory ([diGraph]: a finite type of vertices with a boolean
relation [--]).  χ-boundedness is stated for the class of the underlying graphs of the members of
Forb(S), which is equivalent. *)

From GraphTheory Require Import preliminaries sgraph coloring digraph.
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

(** ** Definitions copied from GraphLib/digraph.v *)

(** [D] is oriented: it has no digon, and no loop. *)
Definition oriented (D : diGraph) : Prop :=
  forall x y : D, x -- y -> ~~ (y -- x).

(** The underlying simple graph of [D]: arcs without direction, loops ignored. *)
Definition underlying (D : diGraph) : sgraph := sgraph_of_rel (@edge_rel D).

(** [D] is an orientation of a star. *)
Definition oriented_star (D : diGraph) : Prop :=
  oriented D /\
  exists c : underlying D,
    (forall v : underlying D, v != c -> c -- v) /\
    (forall u v : underlying D, u != c -> v != c -> u != v -> ~~ (u -- v)).

(** ** Statement *)

Definition AX_oriented_chi_bounded_forbidden_oriented_star : Prop :=
  forall S : diGraph, oriented_star S ->
    chi_bounded (fun G : sgraph =>
      exists2 D : diGraph, oriented D /\ ~ inhabited (S ⇀ D) & G = underlying D).
