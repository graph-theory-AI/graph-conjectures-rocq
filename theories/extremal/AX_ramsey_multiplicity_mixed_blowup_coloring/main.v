(** * Mixed blowup colourings

Fox, Wigderson, "Ramsey multiplicity and the Turán coloring", arXiv:2207.07775, Conjecture 5.3
(2207.07775__01).

The Ramsey number r(k) is the least n such that every colouring of the edges of K_n with two colours
has a monochromatic K_k.  A Ramsey colouring of K_{r(k)-1} is a colouring of its edges with two
colours and no monochromatic K_k.  The blowup K_n[2] is the complete n-partite graph with parts of
size 2.  A mixed blowup colouring of K_{r(k)-1}[2] is a colouring of its edges with two colours and
no monochromatic K_k which is not the blowup of a Ramsey colouring of K_{r(k)-1}.

Conjecture: there is a mixed blowup colouring of K_{r(k)-1}[2] for infinitely many k.

Encoding.  Graphs are finite and simple.  The Ramsey number R = r(k) is given by its
characterization.  A colouring is defined on all sets of vertices, but only its values on the edges
matter.  It is required not to be the blowup of any colouring of K_{R-1}.  This is equivalent, as a
colouring whose blowup has no monochromatic K_k is itself a Ramsey colouring. *)

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

Section CompleteMultipartite.
Variables k m : nat.

(** Vertices in different parts. *)
Definition complete_multipartite_rel : rel ('I_k * 'I_m) := fun x y => x.1 != y.1.

Lemma complete_multipartite_sym : symmetric complete_multipartite_rel.
Proof. by move=> x y; rewrite /complete_multipartite_rel eq_sym. Qed.

Lemma complete_multipartite_irrefl : irreflexive complete_multipartite_rel.
Proof. by move=> x; rewrite /complete_multipartite_rel eqxx. Qed.

(** The complete multipartite graph with [k] parts of size [m]. *)
Definition complete_multipartite : sgraph :=
  SGraph complete_multipartite_sym complete_multipartite_irrefl.

End CompleteMultipartite.

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

(** ** Definitions specific to the conjecture *)

(** The colouring [col] of the edges of [K_n[2]] is the blowup of a colouring of [K_n]: the colour
    of an edge depends only on the parts of its ends. *)
Definition blowup_coloring (n : nat) (col : {set complete_multipartite n 2} -> 'I_2) : Prop :=
  exists chi : {set 'K_n} -> 'I_2,
    forall x y : complete_multipartite n 2, x.1 != y.1 -> col [set x; y] = chi [set x.1; y.1].

(** ** Statement *)

Definition AX_ramsey_multiplicity_mixed_blowup_coloring : Prop :=
  forall N : nat, exists k R : nat,
    [/\ N <= k, ramsey_number 2 (fun _ : 'I_1 => 'K_k) R &
        exists col : {set complete_multipartite R.-1 2} -> 'I_2,
          (forall c : 'I_2, ~ subgraph 'K_k (edge_color_class col (pred1 c))) /\
          ~ blowup_coloring col].
