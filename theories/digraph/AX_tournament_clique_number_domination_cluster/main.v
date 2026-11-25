(** * Clusters of large clique number in tournaments of large domination number

Aboulker, Aubian, Charbit, Lopes, "Clique number of tournaments", 2023, arXiv:2310.04265,
Conjecture 5.3 (2310.04265__07).

A set X of vertices of a tournament T is dominating if every vertex outside X has an in-neighbour
in X.  The domination number dom(T) is the minimum size of a dominating set.

Given a total order ≺ on the vertices of a tournament T, the backedge graph T^≺ is the graph
on V(T) with an edge uv whenever u ≺ v and vu is an arc.  The clique number ω(T) of T is the
minimum over ≺ of the clique number of T^≺.

Conjecture 5.3: there are two functions f and ℓ such that, for every integer k, every tournament T
with dom(T) >= f(k) has a subtournament X with |X| <= ℓ(k) and ω(X) >= k.

Encoding.  Tournaments are digraphs of GraphTheory ([diGraph]: a finite type of vertices with
a boolean relation [--]) satisfying the predicate [tournament].  Vertex orders are given by
permutations, composed with the canonical enumeration of the vertices.  The clique number is
defined for all digraphs. *)

From GraphTheory Require Import sgraph coloring digraph.
From mathcomp Require Import boot perm.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/digraph.v *)

(** [D] is a tournament: it has no loop, and exactly one arc between any two distinct vertices. *)
Definition tournament (D : diGraph) : Prop :=
  irreflexive (@edge_rel D) /\ forall x y : D, (x != y) = (x -- y) (+) (y -- x).

(** [X] dominates [D]: each vertex is in [X] or has an in-neighbour in [X]. *)
Definition out_dominating (D : diGraph) (X : {set D}) : bool :=
  [forall v : D, v \in NS[X]].

(** Domination number. *)
Definition out_domination_number (D : diGraph) : nat :=
  #|[arg min_(X < [set: D] | out_dominating X) #|X|]|.

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

(** ** Statement *)

Definition AX_tournament_clique_number_domination_cluster : Prop :=
  exists f ell : nat -> nat,
    forall (T : diGraph) (k : nat), tournament T -> f k <= out_domination_number T ->
      exists X : {set T}, #|X| <= ell k /\ k <= diclique_number (induced X).
