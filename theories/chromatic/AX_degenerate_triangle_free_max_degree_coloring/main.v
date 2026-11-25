(** * Triangle-free degenerate graphs of bounded maximum degree

Bradač, Fox, Steiner, Sudakov, Zhang, "Coloring small locally sparse degenerate graphs and related
problems", arXiv:2601.15245, Problem 6.2 (2601.15245__02).

A graph is d-degenerate if each of its nonempty subgraphs has a vertex of degree at most d.

Question: is it true that, for every ε > 0, every d-degenerate triangle-free graph G of maximum
degree Δ(G) <= e^(d^(1-ε)) satisfies χ(G) = O(d / log d)?  The positive answer is stated.

Encoding.  It is enough to consider ε = 1/q for the integers q >= 1.  The hypothesis is written
⌊log_2 Δ(G)⌋^q <= d^(q-1) and the conclusion χ(G) ⌊log_2 d⌋ <= C d, where C depends on q; as ε is
arbitrary, the bases and the floors do not matter.  A graph is triangle-free if ω(G) < 3. *)

From GraphTheory Require Import digraph sgraph coloring.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

(** The maximum degree of [G] (0 if [G] is empty). *)
Definition Delta (G : sgraph) : nat := \max_(x : G) #|N(x)|.

(** The subgraph induced by [W] is [k]-degenerate: each nonempty subset [S] of [W] has a
    vertex with at most [k] neighbours in [S]. *)
Definition degenerate_on (G : sgraph) (W : {set G}) (k : nat) : Prop :=
  forall S : {set G}, S \subset W -> S != set0 -> exists x, (x \in S) /\ #|N(x) :&: S| <= k.
Arguments degenerate_on {G} W k.

(** [G] is [k]-degenerate. *)
Definition degenerate (G : sgraph) (k : nat) : Prop :=
  degenerate_on [set: G] k.

(** ** Statement *)

Definition AX_degenerate_triangle_free_max_degree_coloring : Prop :=
  forall q : nat, 0 < q ->
    exists C : nat,
      forall (d : nat) (G : sgraph),
        ω([set: G]) < 3 -> degenerate G d ->
        trunc_log 2 (Delta G) ^ q <= d ^ (q - 1) ->
        χ([set: G]) * trunc_log 2 d <= C * d.
