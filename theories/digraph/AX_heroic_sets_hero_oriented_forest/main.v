(** * Heroic sets made of a hero and an oriented forest

Aboulker, Charbit, Naserasr, "Extension of Gyárfás-Sumner conjecture to digraphs", 2020,
arXiv:2009.13319, Conjecture 4.2 (2009.13319__01).

Digraphs have no loop.  The dichromatic number of a digraph is the minimum number of colours in a
colouring of its vertices such that no colour class contains a directed cycle.  A set of digraphs is
heroic if the digraphs without any induced subdigraph in this set have bounded dichromatic number.
A tournament H is a hero if the tournaments without induced copy of H have bounded dichromatic
number.  An oriented forest is an orientation of a forest, and an oriented star is an orientation
of a star (a tree with at most one vertex of degree more than 1).

Conjecture 4.2: let H be a hero and F be an oriented forest.  The set made of the digon, H and F is
heroic if and only if F is a disjoint union of oriented stars or H is a transitive tournament.

Encoding.  Digraphs are those of GraphTheory ([diGraph]): a finite type of vertices with a boolean
relation [--], without loop or digon here ([oriented]).  Heroes are defined by their recursive
construction, which is equivalent up to isomorphism (theorem of Berger, Choromanski, Chudnovsky,
Fox, Loebl, Scott, Seymour, Thomassé, "Tournaments and colouring", J. Combin. Theory Ser. B 103,
2013).  A forest is a disjoint union of stars if and only if it has no path on four vertices. *)

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

(** ** Definitions copied from GraphLib/digraph.v *)

(** [D] is oriented: it has no digon, and no loop. *)
Definition oriented (D : diGraph) : Prop :=
  forall x y : D, x -- y -> ~~ (y -- x).

(** [D] is a tournament: it has no loop, and exactly one arc between any two distinct vertices. *)
Definition tournament (D : diGraph) : Prop :=
  irreflexive (@edge_rel D) /\ forall x y : D, (x != y) = (x -- y) (+) (y -- x).

(** [D] is a transitive tournament. *)
Definition is_transitive_tournament (D : diGraph) : Prop :=
  tournament D /\ transitive (@edge_rel D).

(** The transitive tournament on [n] vertices. *)
Definition transitive_tournament (n : nat) : diGraph := DiGraph [rel u v : 'I_n | u < v].

(** The underlying simple graph of [D]: arcs without direction, loops ignored. *)
Definition underlying (D : diGraph) : sgraph := sgraph_of_rel (@edge_rel D).

(** D1 => D2: disjoint union, plus all the arcs from [D1] to [D2]. *)
Definition digraph_join (D1 D2 : diGraph) : diGraph :=
  DiGraph (fun x y : D1 + D2 =>
    match x, y with
    | inl a, inl b => a -- b
    | inr a, inr b => a -- b
    | inl _, inr _ => true
    | inr _, inl _ => false
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

(** Heroes (Berger et al., 2013): the tournaments built from a single vertex by the operations
    H1 => H2, Δ(H,TT_k,TT_1) and Δ(TT_k,H,TT_1), where TT_k is the transitive tournament on [k]
    vertices. *)
Inductive hero : diGraph -> Prop :=
| hero_K1 : hero (transitive_tournament 1)
| hero_join (H1 H2 : diGraph) : hero H1 -> hero H2 -> hero (digraph_join H1 H2)
| hero_c3L (H : diGraph) (k : nat) :
    hero H -> hero (c3_subst H (transitive_tournament k) (transitive_tournament 1))
| hero_c3R (H : diGraph) (k : nat) :
    hero H -> hero (c3_subst (transitive_tournament k) H (transitive_tournament 1)).

(** ** Definitions specific to the conjecture *)

(** [G] has no path on four vertices, as a subgraph.  If [G] is a forest, this means that its
    components are stars. *)
Definition no_P4 (G : sgraph) : Prop :=
  ~ exists a b c d : G, [/\ uniq [:: a; b; c; d], a -- b, b -- c & c -- d].

(** ** Statement *)

Definition AX_heroic_sets_hero_oriented_forest : Prop :=
  forall H F : diGraph, hero H -> oriented F -> is_forest [set: underlying F] ->
    dichromatic_bounded (fun D : diGraph =>
      [/\ oriented D, ~ inhabited (H ⇀ D) & ~ inhabited (F ⇀ D)]) <->
    no_P4 (underlying F) \/ is_transitive_tournament H.
