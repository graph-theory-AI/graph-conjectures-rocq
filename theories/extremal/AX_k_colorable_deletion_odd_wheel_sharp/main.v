(** * Making an odd-wheel-free graph k-colourable

Fox, Himwich, Mani, "Making an H-free graph k-colorable", arXiv:2102.10220, conjecture on the
sharpness of Theorem 1.5 (2102.10220__01).

For a graph G, h(G,k) is the minimum number of edges whose deletion makes G k-colourable, and
h(n,k,H) is the maximum of h(G,k) over the graphs G with n vertices that do not contain H as a
subgraph.  The wheel W_l consists of a cycle of length l and a vertex adjacent to all its vertices.

Conjecture: for each r >= 1, the bound h(n,k,W_{2r+1}) <= c_r n^2 / k^(2 - 1/(r+1)) is tight up to
the constant factor c_r depending on r.

Encoding.  Graphs are finite and simple.  The proposition assumes k >= 2, as Theorem 1.5 of the
source.  The source does not give the range of n: the tightness is stated for n sufficiently large
in terms of k, as in the conjecture of the source on K_r (W_3 is K_4), since h(n,k,H) = 0 if n <= k.
The constants depend only on r: they are A for the upper bound (Theorem 1.5) and 1/a for the lower
bound (the conjecture), where a and A are natural numbers.  The threshold n0 depends on r and k.
Inequalities are raised to the power r + 1.  The upper bound on h(n,k,W) says that every W-free
graph with n vertices can be made k-colourable by deleting a small set F of edges, and the lower
bound says that, for some W-free graph with n vertices, every such set F is large. *)

From GraphTheory Require Import preliminaries digraph sgraph coloring.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

Lemma sgraph_of_rel_sym (V : finType) (r : rel V) :
  symmetric (fun x y => (x != y) && sc r x y).
Proof. by move=> x y /=; rewrite eq_sym orbC. Qed.

Lemma sgraph_of_rel_irrefl (V : finType) (r : rel V) :
  irreflexive (fun x y => (x != y) && sc r x y).
Proof. by move=> x; rewrite eqxx. Qed.

(** The graph on [V] whose edges are given by [r], up to symmetry and loops. *)
Definition sgraph_of_rel (V : finType) (r : rel V) : sgraph :=
  SGraph (@sgraph_of_rel_sym V r) (@sgraph_of_rel_irrefl V r).

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

(** The cycle on [n] vertices ([3 <= n] is meant). *)
Definition cycle_graph (n : nat) : sgraph :=
  sgraph_of_rel (fun i j : 'I_n => (val i).+1 %% n == val j).

(** The wheel with [l] spokes: a cycle of length [l] and a vertex adjacent to all its vertices
    ([3 <= l] is meant). *)
Definition wheel (l : nat) : sgraph := add_node (cycle_graph l) [set: cycle_graph l].

(** ** Statement *)

Definition AX_k_colorable_deletion_odd_wheel_sharp : Prop :=
  forall r : nat, 1 <= r -> exists a A : nat, 0 < a /\ 0 < A /\
    forall k : nat, 2 <= k -> exists n0 : nat, forall n : nat, n0 <= n ->
      (forall G : sgraph, #|G| = n -> ~ subgraph (wheel (2 * r + 1)) G ->
         exists F : {set {set G}},
           [/\ F \subset E(G), χ([set: del_edge_set F]) <= k &
               #|F| ^ (r + 1) * k ^ (2 * r + 1) <= (A * n ^ 2) ^ (r + 1)]) /\
      (exists G : sgraph,
         [/\ #|G| = n, ~ subgraph (wheel (2 * r + 1)) G &
             forall F : {set {set G}}, F \subset E(G) -> χ([set: del_edge_set F]) <= k ->
               n ^ (2 * (r + 1)) <= (a * #|F|) ^ (r + 1) * k ^ (2 * r + 1)]).
