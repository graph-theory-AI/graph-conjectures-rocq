(** * Making a K_r-free graph k-colourable

Fox, Himwich, Mani, "Making an H-free graph k-colorable", arXiv:2102.10220, conjecture on the
sharpness of Theorem 1.1 (2102.10220__00).

For a graph G, h(G,k) is the minimum number of edges whose deletion makes G k-colourable, and
h(n,k,H) is the maximum of h(G,k) over the graphs G with n vertices that do not contain H as a
subgraph.

Conjecture: for each r >= 3, if n is sufficiently large in terms of k, then
h(n,k,K_r) = Θ_r(n^2 / k^((r-1)/(r-2))).

Encoding.  Graphs are finite and simple.  The implicit constants depend only on r: they are A for
the upper bound (Theorem 1.1 of the source) and 1/a for the lower bound (the conjecture), where a
and A are natural numbers.  The threshold n0 depends on r and k.  Inequalities are raised to the
power r - 2.  The upper bound on h(n,k,K_r) says that every K_r-free graph with n vertices can be
made k-colourable by deleting a small set F of edges, and the lower bound says that, for some
K_r-free graph with n vertices, every such set F is large. *)

From GraphTheory Require Import digraph sgraph coloring.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

Section DelEdgeSet.
Variables (G : sgraph) (F : {set {set G}}).

(** The edges of [G] that are not in [F]. *)
Definition del_edge_set_rel : rel G := [rel x y : G | (x -- y) && ([set x; y] \notin F)].

Lemma del_edge_set_sym : symmetric del_edge_set_rel.
Proof. by move=> x y; rewrite /del_edge_set_rel /= sg_sym setUC. Qed.

Lemma del_edge_set_irrefl : irreflexive del_edge_set_rel.
Proof. by move=> x; rewrite /del_edge_set_rel /= sg_irrefl. Qed.

(** [G] without the edges of [F]. *)
Definition del_edge_set : sgraph := SGraph del_edge_set_sym del_edge_set_irrefl.

End DelEdgeSet.

(** ** Statement *)

Definition AX_k_colorable_deletion_clique_free_sharp : Prop :=
  forall r : nat, 3 <= r -> exists a A : nat, 0 < a /\ 0 < A /\
    forall k : nat, 0 < k -> exists n0 : nat, forall n : nat, n0 <= n ->
      (forall G : sgraph, #|G| = n -> ~ subgraph 'K_r G ->
         exists F : {set {set G}},
           [/\ F \subset E(G), χ([set: del_edge_set F]) <= k &
               #|F| ^ (r - 2) * k ^ (r - 1) <= (A * n ^ 2) ^ (r - 2)]) /\
      (exists G : sgraph,
         [/\ #|G| = n, ~ subgraph 'K_r G &
             forall F : {set {set G}}, F \subset E(G) -> χ([set: del_edge_set F]) <= k ->
               n ^ (2 * (r - 2)) <= (a * #|F|) ^ (r - 2) * k ^ (r - 1)]).
