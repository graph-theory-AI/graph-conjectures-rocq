(** * Clique number and twin-width of ordered tournaments

Aboulker, Aubian, Charbit, Lopes, "Clique number of tournaments", 2023, arXiv:2310.04265,
Conjecture 3.13 (2310.04265__03).

Given a total order ≺ on the vertices of a tournament T, the backedge graph T^≺ is the graph
on V(T) with an edge uv whenever u ≺ v and vu is an arc.  The clique number ω(T) of T is the
minimum over ≺ of the clique number of T^≺.

A contraction sequence of T is a sequence of partitions of V(T), from the partition into singletons
to a single part, where each step merges two parts.  The error degree of a part X is the number of
other parts Y that are not homogeneous to X.  The twin-width is the minimum over the contraction
sequences of the maximum error degree.  For the twin-width tww(T) of a tournament T, two parts X and
Y are not homogeneous if there are arcs in both directions between them.  For the twin-width
tww(T,≺) of an ordered tournament, they are also not homogeneous if they interleave, that is, if
neither X ≺ Y nor Y ≺ X holds elementwise.

Conjecture 3.13: there exists a function f such that every tournament T has a total order ≺ on its
vertices with ω(T^≺) <= f(ω(T)) and tww(T,≺) <= f(tww(T)).

Encoding.  Tournaments are digraphs of GraphTheory ([diGraph]: a finite type of vertices with a
boolean relation [--]) satisfying the predicate [tournament].  Vertex orders are given by
permutations, composed with the canonical enumeration of the vertices.  The clique number and the
twin-width are defined for all digraphs; two parts X and Y of a tournament are homogeneous if and
only if neither (X,Y) nor (Y,X) is a red pair.  Contraction sequences end with at most one part, so
that the empty tournament is included. *)

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

(** The twin-width of [G] is [t]. *)
Definition twin_width (G : diGraph) (t : nat) : Prop :=
  twin_width_le G t /\ forall m : nat, m < t -> ~ twin_width_le G m.

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

(** The sets [X] and [Y] interleave in the order given by [p]: neither is entirely before
    the other. *)
Definition interleaved (V : finType) (p : {perm V}) (X Y : {set V}) : bool :=
  ~~ [forall x in X, forall y in Y, perm_lt p x y] &&
  ~~ [forall x in X, forall y in Y, perm_lt p y x].

(** The error degree of the part [X] of [P] in the digraph [T] ordered by [p]. *)
Definition ordered_red_degree (T : diGraph) (p : {perm T})
    (P : {set {set T}}) (X : {set T}) : nat :=
  #|[set Y in P | (Y != X) && [|| red_pair X Y, red_pair Y X | interleaved p X Y]]|.

(** The twin-width of the digraph [T] ordered by [p] is at most [d]. *)
Definition ordered_twin_width_le (T : diGraph) (p : {perm T}) (d : nat) : Prop :=
  exists s : seq {set {set T}},
    [/\ path (@merge_parts T) (singletons T) s,
        #|last (singletons T) s| <= 1 &
        forall P : {set {set T}},
          P \in (singletons T :: s) ->
          forall X : {set T}, X \in P -> ordered_red_degree p P X <= d].

(** ** Statement *)

Definition AX_tournament_clique_number_twin_width_ordering : Prop :=
  exists f : nat -> nat,
    forall (T : diGraph) (t : nat), tournament T -> twin_width T t ->
      exists p : {perm T},
        ω([set: backedge_graph p]) <= f (diclique_number T) /\ ordered_twin_width_le p (f t).
