(** * Hedetniemi's conjecture

Hedetniemi, "Homomorphisms of graphs and automata", Technical report, University of Michigan
(1966); Open Problem Garden, hedetniemis_conjecture.

The tensor product (also called direct or categorical product) G × H has vertex set V(G) × V(H),
and (u,v) and (u',v') are adjacent if u, u' are adjacent in G and v, v' are adjacent in H.

Conjecture: if G and H are simple finite graphs, then χ(G × H) = min(χ(G), χ(H)). *)

From GraphTheory Require Import digraph sgraph coloring.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

Section Products.
Variables G H : sgraph.

(** Adjacent in both coordinates. *)
Definition tensor_rel : rel (G * H) :=
  fun p q => (p.1 -- q.1) && (p.2 -- q.2).

Lemma tensor_sym : symmetric tensor_rel.
Proof. by move=> p q; rewrite /tensor_rel ![p.1 -- q.1]sg_sym' ![p.2 -- q.2]sg_sym'. Qed.

Lemma tensor_irrefl : irreflexive tensor_rel.
Proof. by move=> p; rewrite /tensor_rel !sg_irrefl. Qed.

(** The tensor (direct, categorical) product of [G] and [H]. *)
Definition tensor_product : sgraph := SGraph tensor_sym tensor_irrefl.

End Products.

(** ** Statement *)

Definition OPG_hedetniemi_tensor_product_chromatic_min : Prop :=
  forall G H : sgraph,
    χ([set: tensor_product G H]) = minn χ([set: G]) χ([set: H]).
