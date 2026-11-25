(** * Clustered colourings of strong products with paths

Campbell, Gollin, Hendrey, Lesgourgues, Mohar, Tamitegama, Tan, Wood, "Clustered colouring of graph
products", arXiv:2407.21360, Conjecture 7 (2407.21360__00).

A colouring of the vertices, not necessarily proper, has clustering s if its largest monochromatic
component has s vertices.  In the strong product H ⊠ P, distinct pairs are adjacent if they are
equal or adjacent in each coordinate.

Conjecture 7: for every integer c >= 2, there is an integer t such that for infinitely many graphs H
of treewidth t and paths P, every c-colouring of H ⊠ P has clustering Ω(N^(c/(c^2-c+1))), where N is
the number of vertices of H ⊠ P.

Encoding.  "Ω(N^(c/(c^2-c+1)))" means at least N^(c/(c^2-c+1)) / q for a constant q that may depend
on c and t; that is, there is no c-colouring of clustering at most s if
(q s)^(c^2-c+1) < N^c.  "Infinitely many" means that N is unbounded.  The treewidth of H is at most
t, which is equivalent, since a disjoint K_(t+1) can be added to H. *)

From GraphTheory Require Import preliminaries digraph sgraph treewidth.
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

(** The path on [n] vertices. *)
Definition path_graph (n : nat) : sgraph := sgraph_of_rel (fun i j : 'I_n => (val i).+1 == val j).

Section Products.
Variables G H : sgraph.

(** Equal in one coordinate and adjacent in the other. *)
Definition box_rel : rel (G * H) :=
  fun p q => ((p.1 == q.1) && (p.2 -- q.2)) || ((p.2 == q.2) && (p.1 -- q.1)).

Lemma box_sym : symmetric box_rel.
Proof.
by move=> p q; rewrite /box_rel ![p.1 == q.1]eq_sym ![p.2 == q.2]eq_sym
   ![p.1 -- q.1]sg_sym' ![p.2 -- q.2]sg_sym'.
Qed.

Lemma box_irrefl : irreflexive box_rel.
Proof. by move=> p; rewrite /box_rel !eqxx /= !sg_irrefl. Qed.

(** Adjacent in both coordinates. *)
Definition tensor_rel : rel (G * H) :=
  fun p q => (p.1 -- q.1) && (p.2 -- q.2).

Lemma tensor_sym : symmetric tensor_rel.
Proof. by move=> p q; rewrite /tensor_rel ![p.1 -- q.1]sg_sym' ![p.2 -- q.2]sg_sym'. Qed.

Lemma tensor_irrefl : irreflexive tensor_rel.
Proof. by move=> p; rewrite /tensor_rel !sg_irrefl. Qed.

(** Equal or adjacent in each coordinate, and distinct. *)
Definition strong_rel : rel (G * H) :=
  fun p q => box_rel p q || tensor_rel p q.

Lemma strong_sym : symmetric strong_rel.
Proof. by move=> p q; rewrite /strong_rel box_sym tensor_sym. Qed.

Lemma strong_irrefl : irreflexive strong_rel.
Proof. by move=> p; rewrite /strong_rel box_irrefl tensor_irrefl. Qed.

(** The strong product of [G] and [H]. *)
Definition strong_product : sgraph := SGraph strong_sym strong_irrefl.

End Products.

(** ** Definitions copied from GraphLib/chromatic.v *)

(** All elements of [S] have the same colour. *)
Definition monochromatic_on (T : finType) (C : eqType)
    (col : T -> C) (S : {set T}) : bool :=
  constant [seq col x | x <- enum S].

(** [G] has a colouring with [k] colours whose monochromatic components have at most [c]
    vertices. *)
Definition clustered_colorable (G : sgraph) (k c : nat) : Prop :=
  exists col : G -> 'I_k,
    forall S : {set G},
      connected S -> monochromatic_on col S -> #|S| <= c.

(** ** Definitions copied from GraphLib/minor.v *)

(** The treewidth of [G] is at most [k] (the width of a decomposition is, in GraphTheory, the
    maximum size of a bag). *)
Definition treewidth_le (G : sgraph) (k : nat) : Prop :=
  exists (T : forest) (D : T -> {set G}), sdecomp T G D /\ width D <= k.+1.

(** ** Statement *)

Definition AX_clustered_coloring_strong_product_path_tight : Prop :=
  forall c : nat, 2 <= c ->
    exists t q : nat, 0 < q /\
      forall M : nat, exists (H : sgraph) (n : nat),
        [/\ M <= #|H| * n, treewidth_le H t &
            forall s : nat, (q * s) ^ (c ^ 2 - c + 1) < (#|H| * n) ^ c ->
              ~ clustered_colorable (strong_product H (path_graph n)) c s].
