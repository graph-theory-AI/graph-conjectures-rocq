(** * Faithful cycle covers

Seymour; Open Problem Garden, faithful_cycle_covers.

Let G = (V,E) be a graph and p a map from E to the integers.  A list of cycles of G is a faithful
cover of (G,p) if every edge e of G occurs in exactly p(e) cycles of the list.  The map p is
admissible if
- p is nonnegative,
- p(S) is even for every edge cut S (where p(S) is the sum of the p(e) for e in S),
- p(e) <= p(S)/2 for every edge cut S and every edge e of S.

Conjecture: if p is admissible and p(e) is even for every edge e, then (G,p) has a faithful cover.

Encoding.  Graphs are multigraphs with at least one edge (without edges, the empty list is a
faithful cover); loops are allowed, and are cycles.  The map p has values in the natural numbers, so
that nonnegativity is implicit.  Cycles are sets of edges. *)

From GraphTheory Require Import mgraph.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

(** Multigraphs without labels. *)
Abbreviation mgraph := (graph unit unit).

(** The degree of [v] in the edge set [H] (a loop is counted twice). *)
Definition mdeg_in (G : mgraph) (H : {set edge G}) (v : G) : nat :=
  #|[set e in H | source e == v]| + #|[set e in H | target e == v]|.

(** [H] is the edge set of a [k]-regular subgraph. *)
Definition subgraph_kregular (G : mgraph) (H : {set edge G}) (k : nat) : Prop :=
  forall v : G, mdeg_in H v = 0 \/ mdeg_in H v = k.

(** The list of edges [w] is a walk from [x] to [y]; the edges are used in either direction. *)
Fixpoint uwalk (G : mgraph) (x y : G) (w : seq (edge G)) {struct w} : bool :=
  match w with
  | [::] => x == y
  | e :: w' =>
      ((source e == x) && uwalk (target e) y w') ||
      ((target e == x) && uwalk (source e) y w')
  end.

(** [w] is a walk from [x] to [y] with edges in [H]. *)
Definition uwalk_in (G : mgraph) (H : {set edge G}) (x y : G) (w : seq (edge G)) : bool :=
  uwalk x y w && all (fun e => e \in H) w.

(** The vertex [x] is an end of an edge of [H]. *)
Definition subgraph_incident (G : mgraph) (H : {set edge G}) (x : G) : bool :=
  [exists e, (e \in H) && incident x e].

(** The subgraph with edge set [H] and without isolated vertices is connected. *)
Definition subgraph_connected (G : mgraph) (H : {set edge G}) : Prop :=
  forall x y : G, subgraph_incident H x -> subgraph_incident H y -> exists w, uwalk_in H x y w.

(** [C] is the edge set of a cycle of [G] (a loop and a pair of parallel edges are cycles). *)
Definition is_circuit (G : mgraph) (C : {set edge G}) : Prop :=
  [/\ C != set0, subgraph_kregular C 2 & subgraph_connected C].

(** The edges with exactly one end in [S]. *)
Definition mcut (G : mgraph) (S : {set G}) : {set edge G} :=
  [set e | (source e \in S) (+) (target e \in S)].

(** ** Definitions copied from GraphLib/cycle.v *)

Section Decompositions.
Variable G : mgraph.
Implicit Types (C : {set edge G}) (L : seq {set edge G}).

(** [L] is a faithful cycle cover for the weights [p]: each edge [e] is in exactly [p e] cycles
    of [L]. *)
Definition faithful_cycle_cover (p : edge G -> nat) L : Prop :=
  (forall C, C \in L -> is_circuit C) /\
  (forall e : edge G, count (fun C : {set edge G} => e \in C) L = p e).

(** The weights [p] are admissible: each cut has an even total weight, and each of its edges has
    at most half of this weight. *)
Definition admissible_weights (p : edge G -> nat) : Prop :=
  forall (S : {set G}) (e : edge G), e \in mcut S ->
    (2 * p e <= \sum_(f in mcut S) p f)%N /\ ~~ odd (\sum_(f in mcut S) p f).

End Decompositions.

(** ** Statement *)

Definition OPG_faithful_cycle_cover_even_weights : Prop :=
  forall (G : mgraph) (p : edge G -> nat),
    (0 < #|G|)%N -> (0 < #|edge G|)%N -> admissible_weights p ->
    (forall e : edge G, ~~ odd (p e)) ->
    exists L : seq {set edge G}, faithful_cycle_cover p L.
