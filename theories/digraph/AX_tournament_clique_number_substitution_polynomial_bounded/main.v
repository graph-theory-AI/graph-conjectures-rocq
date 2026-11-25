(** * Polynomially χ-bounded classes of tournaments and substitution

Aboulker, Aubian, Charbit, Lopes, "Clique number of tournaments", 2023, arXiv:2310.04265,
Question 3.10 (2310.04265__01).

Given a total order ≺ on the vertices of a tournament T, the backedge graph T^≺ is the graph
on V(T) with an edge uv whenever u ≺ v and vu is an arc.  The clique number ω(T) of T is the
minimum over ≺ of the clique number of T^≺.
The dichromatic number χ(T) is the minimum number of sets in a partition of V(T) into sets that
induce digraphs without directed cycle.
A class of tournaments, closed under subtournaments, is polynomially χ-bounded if there is a
polynomial f such that χ(T) <= f(ω(T)) for every tournament T of the class.

The substitution of T2 for the vertex u of T1 is obtained from the disjoint union of T1 - u
and T2 by adding all arcs from V(T2) to v for each arc uv of T1, and all arcs from v to V(T2) for
each arc vu of T1.  The closure of a class under substitution is the smallest class that contains it
and contains the substitution of T2 for u in T1 for all its members T1, T2 and every vertex u of T1.

Question 3.10: is it true that, if a class of tournaments is polynomially χ-bounded, then so is its
closure under substitution?  The proposition states a positive answer.

Encoding.  Digraphs are those of GraphTheory ([diGraph]: a finite type of vertices with a boolean
relation [--]), and a class is a predicate on them.  The members of the class are assumed to
satisfy the predicate [tournament]; so do then those of its closure.  Classes are not required to
be closed under isomorphism: this does not change the conjecture, since ω and χ are invariant
under isomorphism.  Vertex orders are given by permutations, composed with the canonical
enumeration of the vertices.  The polynomial bounds are of the form c ω^d, which is general
enough: every polynomial is at most c ω^d for some c and d and all ω >= 1, and ω = 0 only for the
empty tournament. *)

From GraphTheory Require Import sgraph coloring digraph.
From mathcomp Require Import boot perm.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/digraph.v *)

(** [D] is a tournament: it has no loop, and exactly one arc between any two distinct vertices. *)
Definition tournament (D : diGraph) : Prop :=
  irreflexive (@edge_rel D) /\ forall x y : D, (x != y) = (x -- y) (+) (y -- x).

(** Substitution of [D2] for the vertex [u] of [D1]. *)
Definition digraph_subst (D1 : diGraph) (u : D1) (D2 : diGraph) : diGraph :=
  DiGraph (fun a b : {x : D1 | x != u} + D2 =>
    match a, b with
    | inl x, inl y => val x -- val y
    | inr x, inr y => x -- y
    | inl x, inr _ => val x -- u
    | inr _, inl y => u -- val y
    end).

(** [D] has no directed cycle: no edge [u -- v] such that [v] reaches [u]
    (a loop or a digon is a directed cycle). *)
Definition acyclic (D : diGraph) : bool :=
  [forall u : D, forall v : D, (u -- v) ==> ~~ connect (--) v u].

(** The dichromatic number, i.e., the least [k] such that the vertices can be coloured with [k]
    colours so that each colour class induces an acyclic digraph. *)
Definition dichromatic_number (D : diGraph) : nat :=
  \big[minn/#|D|]_(k < #|D|.+1 |
     [exists col : {ffun D -> 'I_k}, [forall i : 'I_k, acyclic (induced [set v | col v == i])]])
     (k : nat).

(** [u] is before [v] in the order given by [p]. *)
Definition perm_lt (V : finType) (p : {perm V}) (u v : V) : bool :=
  enum_rank (p u) < enum_rank (p v).

Lemma perm_lt_irrefl (V : finType) (p : {perm V}) : irreflexive (perm_lt p).
Proof. by move=> u; rewrite /perm_lt ltnn. Qed.

(** There is an arc between [u] and [v] that goes backward in the order given by [p]. *)
Definition backedge_rel (D : diGraph) (p : {perm D}) : rel D :=
  [rel u v | perm_lt p u v && (v -- u) || perm_lt p v u && (u -- v)].

Lemma backedge_sym (D : diGraph) (p : {perm D}) : symmetric (backedge_rel p).
Proof. by move=> u v; rewrite /backedge_rel /= orbC. Qed.

Lemma backedge_irrefl (D : diGraph) (p : {perm D}) : irreflexive (backedge_rel p).
Proof. by move=> u; rewrite /backedge_rel /= perm_lt_irrefl. Qed.

(** The backedge graph of [D] in the order given by [p]. *)
Definition backedge_graph (D : diGraph) (p : {perm D}) : sgraph :=
  SGraph (backedge_sym p) (backedge_irrefl p).

(** The clique number of the digraph [D]: the minimum clique number of a backedge graph. *)
Definition diclique_number (D : diGraph) : nat :=
  ω([set: backedge_graph [arg min_(p < (1%g : {perm D})) ω([set: backedge_graph p])]]).

(** The dichromatic number is bounded by a polynomial in the clique number in the class [C]. *)
Definition poly_dichi_bounded (C : diGraph -> Prop) : Prop :=
  exists c d : nat, forall D : diGraph, C D ->
    (dichromatic_number D <= c * diclique_number D ^ d)%N.

(** The class [C] is closed under induced subdigraphs. *)
Definition digraph_induced_closed (C : diGraph -> Prop) : Prop :=
  forall (D : diGraph) (S : {set D}), C D -> C (induced S).

(** The closure of the class [C] under substitution. *)
Inductive subst_closure (C : diGraph -> Prop) : diGraph -> Prop :=
| subst_closure_base (D : diGraph) : C D -> subst_closure C D
| subst_closure_step (D1 : diGraph) (u : D1) (D2 : diGraph) :
    subst_closure C D1 -> subst_closure C D2 -> subst_closure C (digraph_subst u D2).

(** ** Statement *)

Definition AX_tournament_clique_number_substitution_polynomial_bounded : Prop :=
  forall C : diGraph -> Prop,
    digraph_induced_closed C -> (forall T : diGraph, C T -> tournament T) ->
    poly_dichi_bounded C -> poly_dichi_bounded (subst_closure C).
