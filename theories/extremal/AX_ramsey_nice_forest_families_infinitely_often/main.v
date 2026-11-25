(** * Families with a forest are Ramsey-nice infinitely often

Aharoni, Alon, Amir, Haxell, Hefetz, Jiang, Kronenberg, Naor, "Ramsey-nice families of graphs",
arXiv:1708.07369, Conjecture 1.5 (1708.07369__01).

For a finite family F of graphs and an integer k >= 1, the Ramsey number R_k(F) is the least n such
that every colouring of the edges of K_n with k colours contains a monochromatic copy, as a
subgraph, of some member of F.  The family F is k-nice if, for every graph G with chromatic number
R_k(F), every colouring of the edges of G with k colours contains a monochromatic copy of some
member of F.

Conjecture: every finite family of graphs that contains at least one forest is k-nice for infinitely
many integers k.

Encoding.  Graphs are finite and simple.  The family is indexed by 0, ..., r-1.  The colourings are
defined on all sets of vertices, but only the colours of the edges matter. *)

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

(** ** Definitions copied from GraphLib/extremal.v *)

(** [Host] arrows the family [Fam] with [k] colours: each colouring of its edges with [k]
    colours has a monochromatic copy of a graph of [Fam]. *)
Definition ramsey_arrows (Host : sgraph) (k r : nat) (Fam : 'I_r -> sgraph) : Prop :=
  forall col : {set Host} -> 'I_k,
    exists (i : 'I_r) (c : 'I_k), subgraph (Fam i) (edge_color_class col (pred1 c)).

(** The Ramsey number of the family [Fam] with [k] colours is [n]. *)
Definition ramsey_number (k r : nat) (Fam : 'I_r -> sgraph) (n : nat) : Prop :=
  ramsey_arrows 'K_n k Fam /\ forall m : nat, m < n -> ~ ramsey_arrows 'K_m k Fam.

(** The family [Fam] is [k]-nice: the graphs whose chromatic number is the Ramsey number of [Fam]
    with [k] colours arrow [Fam] with [k] colours. *)
Definition ramsey_nice (k r : nat) (Fam : 'I_r -> sgraph) : Prop :=
  forall n : nat, ramsey_number k Fam n ->
    forall G : sgraph, χ([set: G]) = n -> ramsey_arrows G k Fam.

(** ** Statement *)

Definition AX_ramsey_nice_forest_families_infinitely_often : Prop :=
  forall (r : nat) (Fam : 'I_r -> sgraph),
    (exists i : 'I_r, is_forest [set: Fam i]) ->
    forall k0 : nat, exists k : nat, k0 <= k /\ ramsey_nice k Fam.
