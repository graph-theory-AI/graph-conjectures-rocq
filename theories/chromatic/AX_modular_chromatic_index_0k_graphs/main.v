(** * Modular edge-colourings of k-divisible graphs

Berthe, Bonamy, Botler, Carenini, Colucci et al., "On Modular Edge Colourings of Graphs",
arXiv:2507.04254, Conjecture 13 (2507.04254__00).

A 0_k-graph is a graph in which every degree is divisible by k.  A χ'_k-colouring of a graph G is an
edge-colouring in which each colour class has all its non-zero degrees congruent to 1 modulo k.  The
mod k chromatic index χ'_k(G) is the minimum number of colours of such a colouring.

Conjecture 13: for every positive integer k and every 0_k-graph G, χ'_k(G) <= k + o(k).

Encoding.  Graphs are finite and simple.  The term o(k) does not depend on G: for every m > 0,
χ'_k(G) <= (1 + 1/m) k for every sufficiently large k and every 0_k-graph G.  A colouring gives a
colour to every set of vertices, and only the colours of the edges matter.  χ'_k(G) <= b means that
G has a χ'_k-colouring with q <= b colours, where a colour may be unused. *)

From GraphTheory Require Import digraph sgraph.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions specific to the conjecture *)

(** The number of edges at [v] of colour [c]. *)
Definition colour_degree (G : sgraph) (q : nat) (col : {set G} -> 'I_q) (v : G) (c : 'I_q) : nat :=
  \sum_(e in E(G) | (v \in e) && (col e == c)) 1.

(** [G] has a χ'_k-colouring with [q] colours. *)
Definition modular_edge_colourable (G : sgraph) (k q : nat) : Prop :=
  exists col : {set G} -> 'I_q,
    forall (v : G) (c : 'I_q), colour_degree col v c = 0 \/ colour_degree col v c %% k = 1.

(** ** Statement *)

Definition AX_modular_chromatic_index_0k_graphs : Prop :=
  forall m : nat, 0 < m ->
    exists k0 : nat, forall k : nat, k0 <= k ->
      forall G : sgraph, (forall v : G, k %| #|N(v)|) ->
        exists q : nat, m * q <= (m + 1) * k /\ modular_edge_colourable G k q.
