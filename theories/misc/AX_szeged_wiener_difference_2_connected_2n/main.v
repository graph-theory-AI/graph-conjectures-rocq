(** * Difference between the Szeged and the Wiener indices

Bonamy, Knor, Lužar, Pinlou, Škrekovski, "On the difference between the Szeged and Wiener
index", arXiv:1602.05184, Conjecture 5 (1602.05184__00).

Let G be a connected graph.  The Wiener index W(G) is the sum of the distances d(a,b) over the
pairs {a,b} of vertices.  The Szeged index Sz(G) is the sum over the edges ab of the number of
vertices closer to a than to b times the number of vertices closer to b than to a.  Let
η(G) = Sz(G) - W(G), which is nonnegative.  Let K_n^t be the graph obtained from K_{n-1} by
adding a vertex adjacent to t of its vertices.

Conjecture: if G is a 2-connected graph of order n >= 10 that is not isomorphic to K_n, K_n^2
or K_n^{n-2}, then η(G) >= 2n.

Encoding.  The two sums run over the ordered pairs and are halved.  The graph K_n^t is
characterized by a vertex of degree t such that the other vertices form a clique. *)

From GraphTheory Require Import digraph sgraph connectivity.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

(** The vertices of [G] at distance at most [k] from [x]. *)
Definition ball (G : sgraph) (k : nat) (x : G) : {set G} := iter k (@closed_neigh_set G) [set x].

Lemma graph_dist_ex (G : sgraph) (x y : G) :
  exists k : nat, (y \in ball k x) || (k == #|G|).
Proof. by exists #|G|; rewrite eqxx orbT. Qed.

(** The distance of [x] and [y] ([#|G|] if they are in different components). *)
Definition graph_dist (G : sgraph) (x y : G) : nat :=
  ex_minn (graph_dist_ex x y).

(** The Wiener index: the sum of the distances between the pairs of vertices ([G] is
    connected). *)
Definition wiener_index (G : sgraph) : nat :=
  (\sum_(u : G) \sum_(v : G) graph_dist u v) %/ 2.

(** The number of vertices closer to [u] than to [v]. *)
Definition closer_count (G : sgraph) (u v : G) : nat :=
  #|[set x : G | graph_dist x u < graph_dist x v]|.

(** The Szeged index: the sum over the edges [u v] of the number of vertices closer to [u] times
    the number of vertices closer to [v] ([G] is connected). *)
Definition szeged_index (G : sgraph) : nat :=
  (\sum_(u : G) \sum_(v : G | u -- v) closer_count u v * closer_count v u) %/ 2.

(** ** Definitions specific to the conjecture *)

(** The difference [η(G)] of the Szeged and Wiener indices ([G] is connected). *)
Definition eta (G : sgraph) : nat := szeged_index G - wiener_index G.

(** [G] is isomorphic to [K_n^t]. *)
Definition is_K_n_t (G : sgraph) (n t : nat) : Prop :=
  #|G| = n /\
  exists apex : G,
    #|N(apex)| = t /\ cliqueb (~: [set apex]).

(** [G] is isomorphic to [K_n], [K_n^2] or [K_n^(n-2)]. *)
Definition exceptional_graph (G : sgraph) (n : nat) : Prop :=
  inhabited (G ≃ 'K_n) \/
  is_K_n_t G n 2 \/
  is_K_n_t G n (n - 2).

(** ** Statement *)

Definition AX_szeged_wiener_difference_2_connected_2n : Prop :=
  forall (n : nat) (G : sgraph),
    10 <= n ->
    #|G| = n ->
    2.-connected G ->
    ~ exceptional_graph G n ->
    2 * n <= eta G.
