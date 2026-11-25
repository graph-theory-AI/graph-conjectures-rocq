(** * Order of K_r-free d-degenerate graphs of chromatic number d + 1

Bradač, Fox, Steiner, Sudakov, Zhang, "Coloring small locally sparse degenerate graphs and related
problems", arXiv:2601.15245, Problem 6.3 (2601.15245__03).

A graph is d-degenerate if each of its nonempty subgraphs has a vertex of degree at most d; its
chromatic number is then at most d + 1.

Question: is it true that, for a fixed r, the K_r-free d-degenerate graphs of chromatic number d + 1
have e^Ω(d) vertices?  The positive answer is stated.

Encoding.  A graph is K_r-free if ω(G) < r.  The lower bound e^Ω(d) on the number n of vertices is
written d <= m ⌊log_2 n⌋ for d >= d0, where m and d0 depend on r; the base and the floor only change
the constant.  The case r <= 2 is omitted: then d = 0. *)

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

(** ** Statement *)

Definition AX_degenerate_kr_free_extremal_order_exponential : Prop :=
  forall r : nat, 3 <= r ->
    exists m d0 : nat,
      forall (d : nat) (G : sgraph),
        d0 <= d -> ω([set: G]) < r -> degenerate G d -> χ([set: G]) = d.+1 ->
        d <= m * trunc_log 2 #|G|.
