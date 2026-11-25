(** * Irregular spanning subgraphs and minimum degree

Alon, Wei, "Irregular subgraphs", arXiv:2108.02685, Conjecture 1.2 (2108.02685__01).

For a graph H, let m(H,k) denote the number of vertices of degree k in H, and let m(H) denote the
maximum of m(H,k) over all k.

Conjecture 1.2: every graph G with n vertices and minimum degree δ has a spanning subgraph H such
that m(H) <= n/(δ+1) + 2.

Encoding.  H is given by its set of edges, and the inequality is multiplied by δ+1.  The hypothesis
is that the minimum degree is at least δ, which is equivalent. *)

From GraphTheory Require Import digraph sgraph.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

(** Every vertex has degree at least [d] (true if [G] is empty). *)
Definition min_degree_ge (G : sgraph) (d : nat) : Prop := forall v : G, d <= #|N(v)|.

(** The number of members of [F] that contain [v]: the degree of [v] in the hypergraph [F], or
    in the spanning subgraph with edge set [F]. *)
Definition incidence_degree (T : finType) (F : {set {set T}}) (v : T) : nat :=
  #|[set e in F | v \in e]|.

(** The number of vertices of degree [k] in the spanning subgraph of [G] with edge set [F]. *)
Definition degree_class_size (G : sgraph) (F : {set {set G}}) (k : nat) : nat :=
  #|[set v : G | incidence_degree F v == k]|.

(** ** Statement *)

Definition AX_irregular_spanning_subgraph_min_degree : Prop :=
  forall (delta : nat) (G : sgraph),
    min_degree_ge G delta ->
    exists F : {set {set G}},
      F \subset E(G) /\
      forall k : nat, delta.+1 * degree_class_size F k <= #|G| + 2 * delta.+1.
