(** * The tournament Δ(1,2,2) and digraphs without induced K_1 + P_2

Carbonero, Koerts, Moore, Spirkl, "On heroes in digraphs with forbidden induced forests", 2023,
arXiv:2306.04710, open problem (2306.04710__02).

Digraphs have no loop and no digon.  A set of vertices of a digraph is acyclic if it induces a
digraph without directed cycle.  The dichromatic number of a digraph is the minimum number of
acyclic sets that partition its vertices.  A digraph H is a hero in a class of digraphs if the
digraphs of the class without induced copy of H have bounded dichromatic number.  K_1 + P_2 is the
disjoint union of a vertex and an arc.  The tournament Δ(1,2,2) is obtained from a vertex x and two
arcs H_1 and H_2 by adding all the arcs from x to H_1, from H_1 to H_2 and from H_2 to x.

Problem: determine whether Δ(1,2,2) is a hero in the digraphs without induced K_1 + P_2, that is,
whether the digraphs with neither Δ(1,2,2) nor K_1 + P_2 as an induced subdigraph have bounded
dichromatic number.  The proposition states the positive answer.

Encoding.  Digraphs are those of GraphTheory ([diGraph]): a finite type of vertices with a boolean
relation [--], without loop or digon here ([oriented]). *)

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

(** ** Definitions specific to the conjecture *)

(** K_1 + P_2: an isolated vertex and an arc. *)
Definition k1_p2 : diGraph := digraph_sum (transitive_tournament 1) (transitive_tournament 2).

(** ** Statement *)

Definition AX_heroes_delta_1_2_2_k1_p2_free : Prop :=
  dichromatic_bounded (fun D : diGraph =>
    [/\ oriented D, ~ inhabited (k1_p2 ⇀ D) & ~ inhabited (delta_1_2_2 ⇀ D)]).
