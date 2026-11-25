(** * Burr-Erdős conjecture on the Ramsey number of a tree

Burr, Erdős; Bondy, Murty, "Graph Theory", Appendix A, problem 39.

The Ramsey number r(T,T) of a graph T is the least N such that every colouring of the edges of K_N
with two colours contains a monochromatic copy of T, as a subgraph.

Conjecture: r(T,T) <= 2n - 2 for every tree T with n vertices.

Encoding.  Trees have at least two vertices: the Ramsey number of the tree with one vertex is 1.
The inequality r(T,T) <= N means that every colouring of the edges of K_N with two colours contains
a monochromatic copy of T.  The family with the single member T is indexed by 0. *)

From GraphTheory Require Import digraph sgraph.
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

(** ** Definitions copied from GraphLib/chromatic.v *)

(** The spanning subgraph formed by the edges with colour in [p]. *)
Definition edge_color_class (G : sgraph) (C : eqType) (col : {set G} -> C) (p : pred C) : sgraph :=
  del_edge_set [set e : {set G} | ~~ p (col e)].

(** ** Definitions copied from GraphLib/extremal.v *)

(** [Host] arrows the family [Fam] with [k] colours: each colouring of its edges with [k]
    colours has a monochromatic copy of a graph of [Fam]. *)
Definition ramsey_arrows (Host : sgraph) (k r : nat) (Fam : 'I_r -> sgraph) : Prop :=
  forall col : {set Host} -> 'I_k,
    exists (i : 'I_r) (c : 'I_k), subgraph (Fam i) (edge_color_class col (pred1 c)).

(** ** Statement *)

Definition BM_burr_erdos_tree_ramsey_2n_minus_2 : Prop :=
  forall T : sgraph, is_tree [set: T] -> 1 < #|T| ->
    ramsey_arrows 'K_(2 * #|T| - 2) 2 (fun _ : 'I_1 => T).
