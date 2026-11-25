(** * Hat guessing number, degrees and degeneracy

Alon, Ben-Eliezer, Shangguan, Tamo, "The hat guessing number of graphs", arXiv:1812.09752,
Problem 1.4 (1812.09752__00).

In the hat guessing game on G with q colours, each vertex receives a hat with one of the q
colours and sees the hats of its neighbours only.  All vertices simultaneously guess their own
colour, following a strategy fixed in advance, and they win if at least one guess is correct.
The hat guessing number HG(G) is the maximum q for which some strategy wins for every colouring
of the hats.

Problem 1.4: do there exist functions f_1, f_2, f_3 from N to N such that
(i) HG(G) <= f_1(Δ) for every graph G of maximum degree Δ;
(ii) HG(G) <= f_2(d) for every d-degenerate graph G;
(iii) HG(G) >= f_3(δ) for every graph G of minimum degree δ, and f_3 tends to infinity?

The proposition states the positive answer, for the three functions together.

Encoding.  HG(G) >= q is expressed by a winning strategy with q colours, and HG(G) <= m by q <= m
for every such q.  In (iii) some vertex has degree δ, so G is nonempty. *)

From GraphTheory Require Import digraph sgraph.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

(** [P n] holds for every sufficiently large [n]. *)
Definition eventually (P : nat -> Prop) : Prop :=
  exists N : nat, forall n : nat, N <= n -> P n.

(** [f] tends to infinity. *)
Definition tends_to_infinity (f : nat -> nat) : Prop :=
  forall b : nat, eventually (fun n => b <= f n).

(** The maximum degree of [G] (0 if [G] is empty). *)
Definition Delta (G : sgraph) : nat := \max_(x : G) #|N(x)|.

(** Every vertex has degree at least [d] (true if [G] is empty). *)
Definition min_degree_ge (G : sgraph) (d : nat) : Prop := forall v : G, d <= #|N(v)|.

(** The minimum degree of [G] is [d] (false if [G] is empty). *)
Definition min_degree (G : sgraph) (d : nat) : Prop :=
  min_degree_ge G d /\ exists v : G, #|N(v)| = d.

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

Definition AX_hat_guessing_number_degree_degeneracy_bounds : Prop :=
  [/\ (exists f1 : nat -> nat,
         forall G : sgraph, hat_guessing_number_le G (f1 (Delta G))),
      (exists f2 : nat -> nat,
         forall (G : sgraph) (d : nat), degenerate G d -> hat_guessing_number_le G (f2 d))
    & (exists f3 : nat -> nat,
         (forall (G : sgraph) (d : nat), min_degree G d -> hat_guessing_win G (f3 d)) /\
         tends_to_infinity f3)].
