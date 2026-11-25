(** * Largest subgraph without induced even cycle in a sparse graph

Fox, Nenadov, Pham, "The largest subgraph without a forbidden induced subgraph", arXiv:2405.05902,
Conjecture 6.1 (2405.05902__01).

A graph Γ is (c,t)-sparse if e(A,B) <= (1-c)|A||B| for all sets A and B of vertices, not
necessarily disjoint, with |A|, |B| >= t, where e(A,B) is the number of pairs (a,b) of adjacent
vertices with a in A and b in B.  Let P_H be the class of the graphs without induced subgraph
isomorphic to H, and let ex(Γ,P) be the maximum number of edges of a subgraph of Γ that belongs
to P.

Conjecture 6.1: for every c > 0 and every integer ℓ, there is C > 1 such that
ex(Γ, P_(C_2ℓ)) <= C t^(1-1/ℓ) n^(1+1/ℓ) for every (c,t)-sparse graph Γ on n vertices.

Encoding.  ℓ >= 2, so that C_2ℓ is a cycle.  c is a rational number a/b with a <= b: this is
equivalent, as c can be decreased.  C and t are integers, which is equivalent up to a change of C.
The subgraphs of Γ are given by the set F of the edges that are deleted: they are spanning, which
changes nothing since C_2ℓ has no isolated vertex.  The inequality is raised to the power ℓ. *)

From GraphTheory Require Import preliminaries digraph sgraph.
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

(** The number of pairs [(a, b)] of adjacent vertices with [a] in [A] and [b] in [B] (an edge
    with both ends in both sets is counted twice). *)
Definition edge_count_between (G : sgraph) (A B : {set G}) : nat :=
  #|[set p : G * G | [&& p.1 \in A, p.2 \in B & p.1 -- p.2]]|.

(** [G] has an induced subgraph isomorphic to [H]. *)
Definition has_induced_copy (G H : sgraph) : Prop := inhabited (H ⇀ G).

(** [G] has no induced subgraph isomorphic to [H]. *)
Definition induced_free (G H : sgraph) : Prop := ~ has_induced_copy G H.

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

(** ** Definitions specific to the conjecture *)

(** [Gamma] is (c,[t])-sparse for c = [a] / [b]. *)
Definition ct_sparse (Gamma : sgraph) (a b t : nat) : Prop :=
  forall A B : {set Gamma}, t <= #|A| -> t <= #|B| ->
    b * edge_count_between A B <= (b - a) * (#|A| * #|B|).

(** ** Statement *)

Definition AX_sparse_host_hereditary_turan_even_cycles : Prop :=
  forall a b l : nat,
    0 < a -> a <= b -> 2 <= l ->
    exists C : nat,
      1 < C /\
      forall (Gamma : sgraph) (t : nat),
        ct_sparse Gamma a b t ->
        forall F : {set {set Gamma}},
          induced_free (del_edge_set F) (cycle_graph (2 * l)) ->
          #|E(del_edge_set F)| ^ l <= C ^ l * (t ^ l.-1 * #|Gamma| ^ l.+1).
