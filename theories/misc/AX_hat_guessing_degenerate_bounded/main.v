(** * Hat guessing number of degenerate graphs

Alon, Chizewer, "On the hat guessing number of graphs", Discrete Mathematics 345 (2022),
arXiv:2107.05995, informal conjecture (2107.05995__00); question of Alon, Ben-Eliezer,
Shangguan and Tamo.

In the hat guessing game on a graph G, each vertex receives a hat of one of q colours, chosen by
an adversary, and sees only the hats of its neighbours.  All the vertices guess simultaneously
the colours of their own hats, following a deterministic strategy fixed in advance.  They win if
at least one guess is correct.  The hat guessing number HG(G) is the largest q for which they
have a winning strategy.  A graph is d-degenerate if each of its nonempty subgraphs has a vertex
of degree at most d.

Conjecture: there is a function f such that HG(G) <= f(d) for every d-degenerate graph G. *)

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

(** Strategies of the players, who are the vertices: their guesses in [q] colours. *)
Definition hat_strategy (G : sgraph) (q : nat) : Type :=
  G -> {ffun G -> 'I_q} -> 'I_q.

(** Each guess depends only on the colours of the neighbours. *)
Definition sees_only_neighbors (G : sgraph) (q : nat)
    (s : hat_strategy G q) : Prop :=
  forall (v : G) (c c' : {ffun G -> 'I_q}),
    (forall u : G, u -- v -> c u = c' u) -> s v c = s v c'.

(** Some strategy ensures at least one correct guess with [q] colours. *)
Definition hat_guessing_win (G : sgraph) (q : nat) : Prop :=
  exists s : hat_strategy G q,
    sees_only_neighbors s /\
    forall c : {ffun G -> 'I_q}, exists v : G, s v c = c v.

(** The hat guessing number of [G] is at most [m]. *)
Definition hat_guessing_number_le (G : sgraph) (m : nat) : Prop :=
  forall q : nat, hat_guessing_win G q -> (q <= m)%N.

(** ** Statement *)

Definition AX_hat_guessing_degenerate_bounded : Prop :=
  exists f : nat -> nat,
    forall (G : sgraph) (d : nat), degenerate G d -> hat_guessing_number_le G (f d).
