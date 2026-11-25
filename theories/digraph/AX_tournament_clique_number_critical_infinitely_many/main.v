(** * Infinitely many critical tournaments for the clique number

Aboulker, Aubian, Charbit, Lopes, "Clique number of tournaments", 2023, arXiv:2310.04265,
Conjecture 5.10 (2310.04265__10).

Given a total order ≺ on the vertices of a tournament T, the backedge graph T^≺ is the graph
on V(T) with an edge uv whenever u ≺ v and vu is an arc.  The clique number ω(T) of T is the
minimum over ≺ of the clique number of T^≺.  T is k-ω-critical if ω(T) = k and
ω(T - v) = k - 1 for every vertex v.

Conjecture 5.10: for every integer k >= 3, there are infinitely many k-ω-critical tournaments.

Encoding.  Tournaments are digraphs of GraphTheory ([diGraph]: a finite type of vertices with
a boolean relation [--]) satisfying the predicate [tournament].  Vertex orders are given by
permutations, composed with the canonical enumeration of the vertices.  The clique number is
defined for all digraphs.  Infinitely many tournaments (up to isomorphism) means that some
of them are arbitrarily large, as there are finitely many tournaments of each order. *)

From GraphTheory Require Import sgraph coloring digraph.
From mathcomp Require Import boot perm.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/digraph.v *)

(** [D] is a tournament: it has no loop, and exactly one arc between any two distinct vertices. *)
Definition tournament (D : diGraph) : Prop :=
  irreflexive (@edge_rel D) /\ forall x y : D, (x != y) = (x -- y) (+) (y -- x).

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

(** ** Definitions specific to the conjecture *)

(** [T] is k-ω-critical: its clique number is [k], and deleting any vertex makes it [k - 1]. *)
Definition diclique_critical (k : nat) (T : diGraph) : Prop :=
  diclique_number T = k /\ forall v : T, diclique_number (induced [set~ v]) = k - 1.

(** ** Statement *)

Definition AX_tournament_clique_number_critical_infinitely_many : Prop :=
  forall k : nat, 3 <= k ->
    forall N : nat, exists T : diGraph, [/\ tournament T, diclique_critical k T & N < #|T|].
