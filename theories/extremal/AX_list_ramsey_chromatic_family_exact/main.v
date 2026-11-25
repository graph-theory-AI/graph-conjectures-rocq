(** * List Ramsey numbers for graphs of large chromatic number

Fox, He, Luo, Xu, "Multicolor list Ramsey numbers grow exponentially", arXiv:2103.15175, conjecture
on R_l(H_s, k) (2103.15175__00).

For a family H of graphs, the list Ramsey number R_l(H, k) is the minimum n such that, for some
assignment L of lists of k colours to the edges of K_n, every colouring of the edges of K_n from the
lists L contains a monochromatic copy of a graph of H (as a subgraph).

Conjecture: for s >= 2, if H_s is the family of the graphs with chromatic number greater than s,
then R_l(H_s, k) = s^k + 1.

Encoding.  Graphs are finite and simple, and k is positive.  The colours are in an arbitrary finite
type.  The lists and the colourings are defined on all sets of vertices of K_n, but only those of
the edges matter.  There is a monochromatic copy of a graph of H_s if and only if some colour class
has chromatic number greater than s. *)

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

(** ** Definitions copied from GraphLib/chromatic.v *)

(** The spanning subgraph formed by the edges with colour in [p]. *)
Definition edge_color_class (G : sgraph) (C : eqType) (col : {set G} -> C) (p : pred C) : sgraph :=
  del_edge_set [set e : {set G} | ~~ p (col e)].

(** ** Definitions specific to the conjecture *)

(** For some lists of [k] colours on the edges of [Host], each colouring of the edges from these
    lists has a colour class of chromatic number greater than [s]. *)
Definition list_ramsey_chromatic_arrows (Host : sgraph) (k s : nat) : Prop :=
  exists (C : finType) (L : {set Host} -> {set C}),
    (forall e : {set Host}, #|L e| = k) /\
    forall col : {set Host} -> C,
      (forall e : {set Host}, col e \in L e) ->
      exists c : C, s < χ([set: edge_color_class col (pred1 c)]).

(** ** Statement *)

Definition AX_list_ramsey_chromatic_family_exact : Prop :=
  forall s k : nat, 2 <= s -> 0 < k ->
    list_ramsey_chromatic_arrows 'K_(s ^ k).+1 k s /\
    forall n : nat, list_ramsey_chromatic_arrows 'K_n k s -> (s ^ k).+1 <= n.
