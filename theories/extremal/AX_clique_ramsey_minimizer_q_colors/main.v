(** * Clique Ramsey numbers of complete graphs with several colours

Fox, Tidor, Zhang, "Triangle Ramsey numbers of complete graphs", arXiv:2312.06895, generalization of
Conjecture 1.2 to q colours (2312.06895__01).

A graph is K_t-Ramsey for q colours if every colouring of its edges with q colours has a
monochromatic copy of K_t.  The Ramsey number r_q(K_t) is the least n such that K_n is K_t-Ramsey
for q colours.

Conjecture: for all q >= 2 and s <= t, the minimum number of copies of K_s in a graph that is
K_t-Ramsey for q colours is C(r_q(K_t), s) (a binomial coefficient).

Encoding.  Graphs are finite and simple.  The copies of K_s are the cliques on s vertices.  The
Ramsey number R = r_q(K_t) is given by its characterization.  The minimum is C(R, s) when this value
is attained and is a lower bound. *)

From GraphTheory Require Import digraph sgraph coloring.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

(** The number of cliques of [G] on [r] vertices. *)
Definition clique_count_size (G : sgraph) (r : nat) : nat :=
  #|[set S in cliques [set: G] | #|S| == r]|.

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

(** The Ramsey number of the family [Fam] with [k] colours is [n]. *)
Definition ramsey_number (k r : nat) (Fam : 'I_r -> sgraph) (n : nat) : Prop :=
  ramsey_arrows 'K_n k Fam /\ forall m : nat, m < n -> ~ ramsey_arrows 'K_m k Fam.

(** ** Statement *)

Definition AX_clique_ramsey_minimizer_q_colors : Prop :=
  forall q s t : nat, 2 <= q -> s <= t ->
    forall R : nat, ramsey_number q (fun _ : 'I_1 => 'K_t) R ->
      (exists G : sgraph,
         ramsey_arrows G q (fun _ : 'I_1 => 'K_t) /\ clique_count_size G s = 'C(R, s)) /\
      (forall G : sgraph,
         ramsey_arrows G q (fun _ : 'I_1 => 'K_t) -> 'C(R, s) <= clique_count_size G s).
