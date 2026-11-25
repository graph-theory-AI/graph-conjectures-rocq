(** * The tournament Δ(1,2,2) and oriented complete multipartite graphs

Aboulker, Aubian, Charbit, "Heroes in oriented complete multipartite graphs", arXiv:2202.13306,
Question 1.4 (2202.13306__00).

A set of vertices of a digraph is acyclic if it induces a digraph without directed cycle.  The
dichromatic number of a digraph is the minimum number of acyclic sets that partition its vertices.
A digraph H is a hero in a class of digraphs if the digraphs of the class without induced copy of H
have bounded dichromatic number.  An oriented complete multipartite graph is an orientation of a
complete multipartite graph.  The tournament Δ(1,2,2) is obtained from a vertex x and two arcs H_1
and H_2 by adding all the arcs from x to H_1, from H_1 to H_2 and from H_2 to x.

Question 1.4: is Δ(1,2,2) a hero in oriented complete multipartite graphs?  The proposition states
the positive answer.

Encoding.  Digraphs are those of GraphTheory ([diGraph]): a finite type of vertices with a boolean
relation [--], without loop or digon here ([oriented]). *)

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

(** [G] is complete multipartite with parts given by some function. *)
Definition is_complete_multipartite (G : sgraph) : Prop :=
  exists (k : nat) (p : G -> 'I_k), forall x y : G, x -- y = (p x != p y).

(** ** Definitions copied from GraphLib/digraph.v *)

(** [D] is oriented: it has no digon, and no loop. *)
Definition oriented (D : diGraph) : Prop :=
  forall x y : D, x -- y -> ~~ (y -- x).

(** The transitive tournament on [n] vertices. *)
Definition transitive_tournament (n : nat) : diGraph := DiGraph [rel u v : 'I_n | u < v].

(** The underlying simple graph of [D]: arcs without direction, loops ignored. *)
Definition underlying (D : diGraph) : sgraph := sgraph_of_rel (@edge_rel D).

(** Δ(D1,D2,D3): substitution of [D1], [D2], [D3] in the three vertices of a directed triangle
    (all the arcs from [D1] to [D2], from [D2] to [D3] and from [D3] to [D1]). *)
Definition c3_subst (D1 D2 D3 : diGraph) : diGraph :=
  DiGraph (fun x y : D1 + D2 + D3 =>
    match x, y with
    | inl (inl a), inl (inl a') => a -- a'
    | inl (inr b), inl (inr b') => b -- b'
    | inr c, inr c' => c -- c'
    | inl (inl _), inl (inr _) => true
    | inl (inr _), inr _ => true
    | inr _, inl (inl _) => true
    | _, _ => false
    end).

(** Δ(1,2,2): the vertices of a directed triangle are replaced by one vertex, one arc, one arc. *)
Definition delta_1_2_2 : diGraph :=
  c3_subst (transitive_tournament 1) (transitive_tournament 2) (transitive_tournament 2).

(** [D] has no directed cycle: no edge [u -- v] such that [v] reaches [u]
    (a loop or a digon is a directed cycle). *)
Definition acyclic (D : diGraph) : bool :=
  [forall u : D, forall v : D, (u -- v) ==> ~~ connect (--) v u].

(** The dichromatic number of [D] is at most [k]: the vertices can be coloured with [k]
    colours so that each colour class induces an acyclic digraph. *)
Definition dicolorable (D : diGraph) (k : nat) : Prop :=
  exists col : D -> 'I_k, forall i : 'I_k, acyclic (induced [set v | col v == i]).

(** The digraphs of the class [C] have a bounded dichromatic number. *)
Definition dichromatic_bounded (C : diGraph -> Prop) : Prop :=
  exists B : nat, forall D : diGraph, C D -> dicolorable D B.

(** ** Statement *)

Definition AX_heroes_complete_multipartite_delta_1_2_2 : Prop :=
  dichromatic_bounded (fun D : diGraph =>
    [/\ oriented D, is_complete_multipartite (underlying D) & ~ inhabited (delta_1_2_2 ⇀ D)]).
