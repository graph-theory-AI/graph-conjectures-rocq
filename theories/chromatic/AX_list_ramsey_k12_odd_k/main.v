(** * The list Ramsey number of K_{1,2} for an odd number of colours

Alon, Bucić, Kalvari, Kuperwasser, Szabó, "List Ramsey numbers", arXiv:1902.07018 (1902.07018__00).

The list Ramsey number R_l(H,k) is the minimum n such that there is an assignment L of lists of k
colours to the edges of K_n such that every colouring of the edges of K_n from the lists L contains
a monochromatic copy of H (as a subgraph).

Question: is R_l(K_{1,2}, k) equal to k + 1 or k + 2 when k is odd?

The proposition states the answer k + 2, for every odd k.  (A colouring of the edges of K_n has no
monochromatic K_{1,2} if and only if it is proper.  Hence this answer is equivalent to the list
colouring conjecture for the complete graphs K_{k+1} of even order.)

Encoding.  Graphs are finite and simple.  The colours are in an arbitrary finite type.  The lists
and the colourings are defined on all sets of vertices of K_n, but only those of the edges
matter. *)

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

Definition AX_list_ramsey_k12_odd_k : Prop :=
  forall k : nat, odd k -> list_ramsey_number k 'K_1,2 (k + 2).
