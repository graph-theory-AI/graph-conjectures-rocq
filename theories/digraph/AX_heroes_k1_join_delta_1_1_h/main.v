(** * Heroes Δ(1,1,H) in the class of (K_1+F)-free digraphs

Aboulker, Aubian, Charbit, "Heroes in oriented complete multipartite graphs", arXiv:2202.13306,
Question 5.4 (2202.13306__01).

Digraphs have no loop and no digon.  The dichromatic number of a digraph is the minimum number of
sets in a partition of its vertices into sets inducing acyclic subdigraphs.  Forb_ind(F) is the
class of the digraphs without induced subdigraph isomorphic to F.  A digraph H is a hero in a class
C if the digraphs of C without induced subdigraph isomorphic to H have bounded dichromatic number.
K_1 + F is the disjoint union of F and of one vertex.  Δ(1,1,H) is obtained from H by adding two
vertices x and y, the arc xy, all the arcs from y to H and all the arcs from H to x.

Question: if Δ(1,1,H) is a hero in Forb_ind(F) and H is a hero in Forb_ind(K_1 + F), is Δ(1,1,H) a
hero in Forb_ind(K_1 + F)?  The proposition states the positive answer, for all H and F.

Encoding.  Digraphs are those of GraphTheory ([diGraph]: a finite type of vertices with a boolean
relation [--]), and the absence of loops and digons is the predicate [oriented].  K_1 is the
transitive tournament on one vertex, Δ is [c3_subst] and + is [digraph_sum]. *)

From GraphTheory Require Import digraph.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/digraph.v *)

(** [D] is oriented: it has no digon, and no loop. *)
Definition oriented (D : diGraph) : Prop :=
  forall x y : D, x -- y -> ~~ (y -- x).

(** The transitive tournament on [n] vertices. *)
Definition transitive_tournament (n : nat) : diGraph := DiGraph [rel u v : 'I_n | u < v].

(** Disjoint union. *)
Definition digraph_sum (D1 D2 : diGraph) : diGraph :=
  DiGraph (fun x y : D1 + D2 =>
    match x, y with
    | inl a, inl b => a -- b
    | inr a, inr b => a -- b
    | _, _ => false
    end).

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

(** ** Definitions specific to the conjecture *)

(** The class Forb_ind(F), among the digraphs without loop and digon. *)
Definition Forb_ind (F D : diGraph) : Prop := oriented D /\ ~ inhabited (F ⇀ D).

(** [H] is a hero in the class [C]. *)
Definition hero_in (C : diGraph -> Prop) (H : diGraph) : Prop :=
  dichromatic_bounded (fun D => C D /\ ~ inhabited (H ⇀ D)).

(** K_1. *)
Definition K1 : diGraph := transitive_tournament 1.

(** ** Statement *)

Definition AX_heroes_k1_join_delta_1_1_h : Prop :=
  forall H F : diGraph, oriented H -> oriented F ->
    hero_in (Forb_ind F) (c3_subst K1 K1 H) ->
    hero_in (Forb_ind (digraph_sum K1 F)) H ->
    hero_in (Forb_ind (digraph_sum K1 F)) (c3_subst K1 K1 H).
