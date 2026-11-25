(** * Strong Erdős-Hajnal property of the tournaments with at most three backedges

Chudnovsky, Scott, Seymour, Spirkl, "Pure pairs. X. Tournaments and the strong Erdős-Hajnal
property", 2022, arXiv:2202.13977, question after Theorem 1.6 (2202.13977__01).

A tournament G is H-free if it has no subtournament isomorphic to H.  A tournament H has the strong
EH-property if there is c > 0 such that every H-free tournament G with |G| > 1 has disjoint sets of
vertices A and B, with all arcs directed from A to B, such that min(|A|,|B|) >= c|G|.
A numbering of H is an ordering v_1, ..., v_n of its vertices; its backedge graph is the graph on
V(H) where, for i < j, v_i v_j is an edge (a backedge) if the arc of H is directed from v_j to v_i.
D_5 is the 5-vertex tournament in which every vertex has out-degree two.

The authors prove that a tournament has the strong EH-property if it is D_5-free and admits a
numbering for which the backedge graph has at most three edges.  Question: can the condition that it
is D_5-free be omitted?  The proposition states a positive answer: every tournament which admits a
numbering with at most three backedges has the strong EH-property.

Encoding.  Tournaments are digraphs of GraphTheory ([diGraph]: a finite type of vertices with
a boolean relation [--]) satisfying the predicate [tournament], and H ⇀ G is the type of the
isomorphisms from H to an induced subdigraph of G.  Numberings are given by permutations, composed
with the canonical enumeration of the vertices.  The constant c is taken of the form 1/q where q is
a positive integer, without loss of generality. *)

From GraphTheory Require Import sgraph digraph.
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

(** The strong Erdős-Hajnal property of the tournament [H]: each [H]-free tournament [G] with at
    least two vertices has disjoint sets [A], [B] of linear size with all arcs from [A] to [B]. *)
Definition strong_EH_tournament (H : diGraph) : Prop :=
  exists q : nat, 1 <= q /\
    forall G : diGraph, tournament G -> ~ inhabited (H ⇀ G) -> 1 < #|G| ->
      exists A B : {set G}, [/\ [disjoint A & B], (forall a b, a \in A -> b \in B -> a -- b),
        #|G| <= q * #|A| & #|G| <= q * #|B|].

(** ** Statement *)

Definition AX_tournament_strong_eh_three_backedges_d5 : Prop :=
  forall H : diGraph, tournament H ->
    (exists p : {perm H}, #|E(backedge_graph p)| <= 3) -> strong_EH_tournament H.
