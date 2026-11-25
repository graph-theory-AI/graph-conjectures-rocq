(** * Clustered 3-colourings of strong products

Campbell, Gollin, Hendrey, Lesgourgues, Mohar, Tamitegama, Tan, Wood, "Clustered colouring of graph
products", arXiv:2407.21360, Conjecture 8 (2407.21360__01).

A colouring of the vertices, not necessarily proper, has clustering s if its largest monochromatic
component has s vertices.  In the strong product H_1 ⊠ H_2, distinct pairs are adjacent if they are
equal or adjacent in each coordinate.

Conjecture 8: there is an integer t >= 1 such that for infinitely many pairs (H_1,H_2) of graphs of
treewidth t, every 3-colouring of H_1 ⊠ H_2 has clustering Ω(N^(4/7)), where N is the number of
vertices of H_1 ⊠ H_2.

Encoding.  "Ω(N^(4/7))" means at least N^(4/7) / q for a constant q; that is, there is no
3-colouring of clustering at most s if (q s)^7 < N^4.  "Infinitely many pairs" means that N is
unbounded.  The treewidth of H_1 and H_2 is at most t, which is equivalent, since a disjoint K_(t+1)
can be added to each of them. *)

From GraphTheory Require Import digraph sgraph treewidth.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

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

Definition AX_clustered_coloring_strong_product_exponent_tight : Prop :=
  exists t q : nat,
    [/\ 0 < t, 0 < q &
        forall M : nat, exists H1 H2 : sgraph,
          [/\ M <= #|H1| * #|H2|, treewidth_le H1 t, treewidth_le H2 t &
              forall s : nat, (q * s) ^ 7 < (#|H1| * #|H2|) ^ 4 ->
                ~ clustered_colorable (strong_product H1 H2) 3 s]].
