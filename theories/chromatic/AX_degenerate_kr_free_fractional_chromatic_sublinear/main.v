(** * Fractional chromatic number of K_r-free d-degenerate graphs

Bradač, Fox, Steiner, Sudakov, Zhang, "Coloring small locally sparse degenerate graphs and related
problems", arXiv:2601.15245, Problem 6.4 (2601.15245__04).

A graph is d-degenerate if each nonempty subgraph has a vertex of degree at most d.  The fractional
chromatic number χ_f(G) is the minimum of a / b such that G has a b-fold colouring with a colours:
each vertex receives b of the a colours, and adjacent vertices receive disjoint sets.

Problem: let r >= 4.  Is it true that the maximum fractional chromatic number of K_r-free
d-degenerate graphs is o_r(d)?

The proposition states the positive answer.

Encoding.  Graphs are finite and simple.  The bound o_r(d) means that, for every r and every
ε = 1/q, χ_f(G) <= ε d for all d >= d_0, where d_0 depends on r and q. *)

From GraphTheory Require Import digraph sgraph coloring.
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

(** There is a weighted colouring with [k] colours: each vertex [v] receives a set of [p v]
    colours, and adjacent vertices receive disjoint sets. *)
Definition weighted_colorable (G : sgraph) (p : G -> nat) (k : nat) : Prop :=
  exists f : G -> {set 'I_k},
    (forall v : G, #|f v| = p v) /\
    (forall x y : G, x -- y -> [disjoint f x & f y]).

(** ** Definitions copied from GraphLib/fractional.v *)

(** The fractional chromatic number of [G] is at most [p / q] ([0 < q] is meant): [G] has a
    [b]-fold colouring with [a] colours (each vertex receives [b] colours, and adjacent vertices
    receive disjoint sets) such that [a / b <= p / q]. *)
Definition fractional_chromatic_le (G : sgraph) (p q : nat) : Prop :=
  exists a b : nat, [/\ 0 < b, weighted_colorable (fun _ : G => b) a & a * q <= p * b].

(** ** Statement *)

Definition AX_degenerate_kr_free_fractional_chromatic_sublinear : Prop :=
  forall r : nat, 4 <= r ->
    forall q : nat, 0 < q ->
      exists d0 : nat,
        forall (d : nat) (G : sgraph),
          d0 <= d ->
          ω([set: G]) < r ->
          degenerate G d ->
          fractional_chromatic_le G d q.
