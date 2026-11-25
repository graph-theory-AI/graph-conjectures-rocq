(** * Orderings optimal for both the clique number and the dichromatic number

Aboulker, Aubian, Charbit, Lopes, "Clique number of tournaments", 2023, arXiv:2310.04265,
Question 3.5 (2310.04265__00).

Given a total order ≺ on the vertices of a tournament T, the backedge graph T^≺ is the graph
on V(T) with an edge uv whenever u ≺ v and vu is an arc.  The clique number ω(T) of T is the
minimum over ≺ of the clique number of T^≺.
The dichromatic number χ(T) is the minimum number of sets in a partition of V(T) into sets that
induce digraphs without directed cycle.
It is also the minimum over ≺ of the chromatic number of T^≺.  The order ≺ is an ω-ordering if
ω(T^≺) = ω(T), and a χ-ordering if χ(T^≺) = χ(T).

Question 3.5: is it true that every tournament has an ordering of its vertices which is both an
ω-ordering and a χ-ordering?  The proposition states a positive answer.

Encoding.  Tournaments are digraphs of GraphTheory ([diGraph]: a finite type of vertices with
a boolean relation [--]) satisfying the predicate [tournament].  Vertex orders are given by
permutations, composed with the canonical enumeration of the vertices.  The clique number and
the dichromatic number are defined for all digraphs.  In the statement, ω([set: G]) and
χ([set: G]) are the clique number and the chromatic number of the graph G in GraphTheory. *)

From GraphTheory Require Import sgraph coloring digraph.
From mathcomp Require Import boot perm.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/digraph.v *)

(** [D] is a tournament: it has no loop, and exactly one arc between any two distinct vertices. *)
Definition tournament (D : diGraph) : Prop :=
  irreflexive (@edge_rel D) /\ forall x y : D, (x != y) = (x -- y) (+) (y -- x).

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

(** ** Statement *)

Definition AX_tournament_clique_number_simultaneous_ordering : Prop :=
  forall T : diGraph, tournament T ->
    exists p : {perm T},
      ω([set: backedge_graph p]) = diclique_number T /\
      χ([set: backedge_graph p]) = dichromatic_number T.
