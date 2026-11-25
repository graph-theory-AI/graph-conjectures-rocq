(** * Hat guessing number after adding a universal vertex

Alon, Chizewer, "On the hat guessing number of graphs", arXiv:2107.05995, open problems
(2107.05995__02).

In the hat guessing game on G with q colours, each vertex receives a hat with one of the q
colours and sees the hats of its neighbours only.  All vertices simultaneously guess their own
colour, following a strategy fixed in advance, and they win if at least one guess is correct.
The hat guessing number HG(G) is the maximum q for which some strategy wins for every colouring
of the hats.

Problem: give an upper bound for HG(G') as a function of HG(G), where G' is obtained from G by
adding a vertex adjacent to all the vertices of G, or show that no such function exists.

The proposition states the first answer: there is a function f such that HG(G') <= f(m) for every
graph G with HG(G) <= m.

Encoding.  HG(G) <= m means that q <= m for every q such that some strategy wins with q colours.
Taking HG(G) = m as hypothesis would be equivalent, up to replacing f(m) by the maximum of f(0),
..., f(m). *)

From GraphTheory Require Import digraph sgraph.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

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

Definition AX_hat_guessing_universal_vertex_addition : Prop :=
  exists f : nat -> nat,
    forall (G : sgraph) (m : nat),
      hat_guessing_number_le G m -> hat_guessing_number_le (add_node G [set: G]) (f m).
