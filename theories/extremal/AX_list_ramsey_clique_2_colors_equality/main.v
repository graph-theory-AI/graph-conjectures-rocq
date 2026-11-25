(** * List Ramsey numbers of cliques with two colours

Alon, Bucić, Kalvari, Kuperwasser, Szabó, "List Ramsey numbers", arXiv:1902.07018, open problem on
the equality of R_l(K_r,2) and R(K_r,2) (1902.07018__01).

The Ramsey number R(H,k) is the minimum n such that every colouring of the edges of K_n with k
colours contains a monochromatic copy of H (as a subgraph).  The list Ramsey number R_l(H,k) is the
minimum n such that there is an assignment L of lists of k colours to the edges of K_n such that
every colouring of the edges of K_n from the lists L contains a monochromatic copy of H.

Question: is R_l(K_r,2) = R(K_r,2) for all r > 3?  The proposition states that the answer is yes.

Encoding.  Graphs are finite and simple.  The lists and the colourings are defined on all sets of
vertices of K_n, but only those of the edges matter, and the colours of the lists are in an
arbitrary finite type.  In [ramsey_number], the family with the single member K_r is indexed
by 0. *)

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

(** The Ramsey number of the family [Fam] with [k] colours is [n]. *)
Definition ramsey_number (k r : nat) (Fam : 'I_r -> sgraph) (n : nat) : Prop :=
  ramsey_arrows 'K_n k Fam /\ forall m : nat, m < n -> ~ ramsey_arrows 'K_m k Fam.

(** For some lists of [k] colours on the edges of [Host], each colouring of the edges from these
    lists has a monochromatic copy of [H]. *)
Definition list_ramsey_arrows (Host : sgraph) (k : nat) (H : sgraph) : Prop :=
  exists (C : finType) (L : {set Host} -> {set C}),
    (forall e : {set Host}, #|L e| = k) /\
    forall col : {set Host} -> C,
      (forall e : {set Host}, col e \in L e) ->
      exists c : C, subgraph H (edge_color_class col (pred1 c)).

(** The list Ramsey number of [H] with [k] colours is [n] ([0 < k] is meant). *)
Definition list_ramsey_number (k : nat) (H : sgraph) (n : nat) : Prop :=
  list_ramsey_arrows 'K_n k H /\ forall m : nat, m < n -> ~ list_ramsey_arrows 'K_m k H.

(** ** Statement *)

Definition AX_list_ramsey_clique_2_colors_equality : Prop :=
  forall r n : nat, 3 < r ->
    list_ramsey_number 2 'K_r n <-> ramsey_number 2 (fun _ : 'I_1 => 'K_r) n.
