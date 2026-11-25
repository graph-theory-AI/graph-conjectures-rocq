(** * Nearly spanning regular subgraphs

Alon, Mubayi; Alon, "Problems and results in extremal combinatorics", Discrete Math. 273 (2003);
Open Problem Garden, nearly_spanning_regular_subgraphs.

Conjecture: for every ε > 0 and every positive integer k, there is an r_0 such that every simple
r-regular graph G with r >= r_0 has a k-regular subgraph H with |V(H)| >= (1 - ε) |V(G)|.

Encoding.  The number ε = p/q is rational, which is not a restriction.  The inequality is multiplied
by q; the truncated subtraction q - p is 0 for ε >= 1, where the conclusion is clear (H can be
empty).  The subgraph H is given up to isomorphism. *)

From GraphTheory Require Import digraph sgraph.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

(** Every vertex has degree [d]. *)
Definition regular (G : sgraph) (d : nat) : Prop := forall v : G, #|N(v)| = d.

(** ** Statement *)

Definition OPG_regular_nearly_spanning_k_regular_subgraph : Prop :=
  forall p q k : nat, 0 < p -> 0 < q -> 0 < k ->
    exists r0 : nat, forall (r : nat) (G : sgraph),
      r0 <= r -> regular G r ->
      exists H : sgraph, [/\ subgraph H G, regular H k & (q - p) * #|G| <= q * #|H|].
