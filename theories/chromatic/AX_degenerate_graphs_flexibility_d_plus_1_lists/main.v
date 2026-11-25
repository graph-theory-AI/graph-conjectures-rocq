(** * Flexibility of degenerate graphs with lists of size d+1

Dvořák, Norin, Postle, "List coloring with requests", J. Graph Theory 92 (2019),
arXiv:1612.08698, Problem 1 (1612.08698__00).

Let L be an assignment of lists of colours to the vertices of a graph G.  An L-colouring is a
proper colouring f such that f(v) ∈ L(v) for every vertex v.  A weighted request gives a nonnegative
weight w(v,c) to each vertex v and each colour c ∈ L(v).  G with L is weighted ε-flexible if for
every weighted request w, some L-colouring f satisfies Σ_v w(v,f(v)) >= ε Σ_{v, c ∈ L(v)} w(v,c).
G is d-degenerate if every nonempty induced subgraph has a vertex of degree at most d.

Problem 1: does there exist, for every integer d >= 0, some ε > 0 such that every d-degenerate
graph with an assignment of lists of size d+1 is weighted ε-flexible?

The proposition states the positive answer.

Encoding.  Graphs are finite and simple.  ε is a rational number p/q with 0 < p <= q, and weights
are natural numbers.  This is equivalent to the problem with real numbers: ε may be decreased,
weights may be multiplied by a constant, and rational weights suffice by approximation.  The authors
also ask whether the weaker (unweighted) ε-flexibility holds; it is not stated. *)

From GraphTheory Require Import digraph sgraph.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

(** The subgraph induced by [W] is [k]-degenerate: each nonempty subset [S] of [W] has a
    vertex with at most [k] neighbours in [S]. *)
Definition degenerate_on (G : sgraph) (W : {set G}) (k : nat) : Prop :=
  forall S : {set G}, S \subset W -> S != set0 -> exists x, (x \in S) /\ #|N(x) :&: S| <= k.
Arguments degenerate_on {G} W k.

(** [G] is [k]-degenerate. *)
Definition degenerate (G : sgraph) (k : nat) : Prop :=
  degenerate_on [set: G] k.

(** ** Definitions copied from GraphLib/chromatic.v *)

(** [f] is a proper colouring from the lists [L]. *)
Definition proper_list_coloring
    (G : sgraph) (C : finType) (L : G -> {set C}) (f : G -> C) : Prop :=
  (forall v : G, f v \in L v) /\
  (forall x y : G, x -- y -> f x != f y).

(** The total weight of the requests [w] (the vertex [v] requests the colour [c] with weight
    [w v c]), for the colours in the lists [L]. *)
Definition total_request_weight
    (G : sgraph) (C : finType) (L : G -> {set C}) (w : G -> C -> nat) : nat :=
  \sum_(v : G) \sum_(c in L v) w v c.

(** The weight of the requests satisfied by the colouring [f]. *)
Definition satisfied_request_weight
    (G : sgraph) (C : finType) (w : G -> C -> nat) (f : G -> C) : nat :=
  \sum_(v : G) w v (f v).

(** [G] is weighted [p/q]-flexible for lists of size [k]: for all requests, some proper list
    colouring satisfies a proportion at least [p/q] of their weight. *)
Definition weighted_flexible (G : sgraph) (k p q : nat) : Prop :=
  forall (C : finType) (L : G -> {set C}) (w : G -> C -> nat),
    (forall v : G, #|L v| = k) ->
    exists f : G -> C,
      proper_list_coloring L f /\
      p * total_request_weight L w <= q * satisfied_request_weight w f.

(** ** Statement *)

Definition AX_degenerate_graphs_flexibility_d_plus_1_lists : Prop :=
  forall d : nat,
    exists p q : nat,
      [/\ 0 < p, p <= q
        & forall G : sgraph, degenerate G d -> weighted_flexible G d.+1 p q].
