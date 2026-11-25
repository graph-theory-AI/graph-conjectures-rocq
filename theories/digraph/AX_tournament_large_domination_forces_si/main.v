(** * Tournaments with large domination number contain S_i

Harutyunyan, Le, Thomassé, Wu, "Coloring tournaments: from local to global", 2017,
arXiv:1702.01607, Problem 3 (1702.01607__00).

A set S of vertices of a tournament T is dominating if every vertex outside S has an in-neighbour
in S.  The dominating number of T is the minimum size of a dominating set.  S_1 is the one-vertex
tournament and, for i > 1, S_i is obtained from a directed triangle by substituting S_{i-1} for
two of its vertices.

Problem 3: for every integer i >= 1, there exists f(i) such that every tournament with dominating
number at least f(i) contains an isomorphic copy of S_i.

Encoding.  Tournaments are digraphs of GraphTheory ([diGraph]: a finite type of vertices with a
boolean relation [--]) satisfying the predicate [tournament].  The recursive definition of S_i
starts from the empty tournament S_0, so that S_1 has one vertex. *)

From GraphTheory Require Import digraph.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/digraph.v *)

(** [D] is a tournament: it has no loop, and exactly one arc between any two distinct vertices. *)
Definition tournament (D : diGraph) : Prop :=
  irreflexive (@edge_rel D) /\ forall x y : D, (x != y) = (x -- y) (+) (y -- x).

(** The transitive tournament on [n] vertices. *)
Definition transitive_tournament (n : nat) : diGraph := DiGraph [rel u v : 'I_n | u < v].

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

(** [X] dominates [D]: each vertex is in [X] or has an in-neighbour in [X]. *)
Definition out_dominating (D : diGraph) (X : {set D}) : bool :=
  [forall v : D, v \in NS[X]].

(** Domination number. *)
Definition out_domination_number (D : diGraph) : nat :=
  #|[arg min_(X < [set: D] | out_dominating X) #|X|]|.

(** ** Definitions specific to the conjecture *)

(** The tournament S_i, on 2^i - 1 vertices. *)
Fixpoint S_tournament (i : nat) : diGraph :=
  if i is j.+1 then c3_subst (S_tournament j) (S_tournament j) (transitive_tournament 1)
  else transitive_tournament 0.

(** ** Statement *)

(** A tournament T with a large dominating number contains S_i. *)
Definition AX_tournament_large_domination_forces_si : Prop :=
  forall i : nat, 0 < i ->
    exists f : nat, forall T : diGraph, tournament T ->
      f <= out_domination_number T -> inhabited (S_tournament i ⇀ T).
