(** * χ-boundedness of the tournaments of bounded twin-width

Aboulker, Aubian, Charbit, Lopes, "Clique number of tournaments", 2023, arXiv:2310.04265,
Conjecture 3.12 (2310.04265__02).

Given a total order ≺ on the vertices of a tournament T, the backedge graph T^≺ is the graph
on V(T) with an edge uv whenever u ≺ v and vu is an arc.  The clique number ω(T) of T is the
minimum over ≺ of the clique number of T^≺.
The dichromatic number χ(T) is the minimum number of sets in a partition of V(T) into sets that
induce digraphs without directed cycle.  A class of tournaments is χ-bounded if there is a function
f such that χ(T) <= f(ω(T)) for every T in the class.

A contraction sequence of T is a sequence of partitions of V(T), from the partition into singletons
to a single part, where each step merges two parts.  The error degree of a part X is the number of
other parts Y such that there are arcs in both directions between X and Y.  The twin-width of T is
the minimum over the contraction sequences of the maximum error degree.

Conjecture 3.12: for every k >= 1, the class of tournaments of twin-width at most k is χ-bounded.

Encoding.  Tournaments are digraphs of GraphTheory ([diGraph]: a finite type of vertices with a
boolean relation [--]) satisfying the predicate [tournament].  Vertex orders are given by
permutations, composed with the canonical enumeration of the vertices.  The clique number and the
twin-width are defined for all digraphs; there are arcs in both directions between two parts X and Y
of a tournament if and only if (X,Y) or (Y,X) is a red pair.  Contraction sequences end with at most
one part, so that the empty tournament is included. *)

From GraphTheory Require Import sgraph coloring digraph.
From mathcomp Require Import boot order perm.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/minor.v *)

(** There are both edges and non-edges from [X] to [Y]. *)
Definition red_pair (G : diGraph) (X Y : {set G}) : bool :=
  [exists x in X, exists y in Y, x -- y] && [exists x in X, exists y in Y, ~~ (x -- y)].

(** The red degree of the part [X] of [P]. *)
Definition red_degree (G : diGraph) (P : {set {set G}}) (X : {set G}) : nat :=
  #|[set Y in P | (Y != X) && (red_pair X Y || red_pair Y X)]|.

(** The partition into singletons. *)
Definition singletons (G : diGraph) : {set {set G}} := [set [set x] | x : G].

(** [Q] is obtained from [P] by merging two parts. *)
Definition merge_parts (G : diGraph) (P Q : {set {set G}}) : bool :=
  [exists X in P, exists Y in P, (X != Y) && (Q == (X :|: Y) |: (P :\ X :\ Y))].

(** The twin-width of the graph or digraph [G] is at most [d]: some sequence of merges from the
    partition into singletons to a single part has red degrees at most [d]. *)
Definition twin_width_le (G : diGraph) (d : nat) : Prop :=
  exists s : seq {set {set G}},
    [/\ path (@merge_parts G) (singletons G) s,
        #|last (singletons G) s| <= 1 &
        forall P : {set {set G}},
          P \in (singletons G :: s) ->
          forall X : {set G}, X \in P -> red_degree P X <= d].

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

(** The dichromatic number is bounded by a function of the clique number in the class [C]. *)
Definition dichi_bounded (C : diGraph -> Prop) : Prop :=
  exists f : nat -> nat, forall D : diGraph, C D ->
    (dichromatic_number D <= f (diclique_number D))%N.

(** ** Statement *)

Definition AX_tournament_clique_number_twin_width_bounded : Prop :=
  forall k : nat, 1 <= k ->
    dichi_bounded (fun T : diGraph => tournament T /\ twin_width_le T k).
