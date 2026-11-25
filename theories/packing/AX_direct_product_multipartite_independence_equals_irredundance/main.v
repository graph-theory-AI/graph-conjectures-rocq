(** * Upper irredundance number of direct products of complete multipartite graphs

Alon, Defant, "Isoperimetry, Stability, and Irredundance in Direct Products", arXiv:1904.02595,
Conjecture 1.2 (1904.02595__00).

The direct (tensor) product of graphs H_1, ..., H_n has vertex set V(H_1) x ... x V(H_n), and two of
its vertices are adjacent if they are adjacent in every coordinate.  For a set S of vertices, N[S]
is its closed neighbourhood.  S is irredundant if N[S - v] <> N[S] for every v in S.  The upper
irredundance number IR(G) is the maximum size of an irredundant set of G.

Conjecture: if G is the direct product of complete multipartite graphs H_1, ..., H_n, then
α(G) = IR(G).

Encoding.  Graphs are finite and simple.  The factors are indexed by 0, ..., n, so that there is at
least one.  The product is nested: H_0 x (H_1 x (... x H_n)).  Parts of complete multipartite graphs
may have different sizes, and some may be empty.  A single part is allowed, which adds only trivial
cases (the product has no edge).  [irredundant] and [IR] are those of GraphTheory, where the
condition N[S - v] <> N[S] is written: some vertex of N[v] is not in N[S - v]. *)

From GraphTheory Require Import digraph sgraph coloring dom.
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

(** [G] is complete multipartite with parts given by some function. *)
Definition is_complete_multipartite (G : sgraph) : Prop :=
  exists (k : nat) (p : G -> 'I_k), forall x y : G, x -- y = (p x != p y).

(** ** Definitions specific to the conjecture *)

(** The direct product of [H 0], ..., [H n]. *)
Fixpoint tensor_product_family (n : nat) : ('I_n.+1 -> sgraph) -> sgraph :=
  match n with
  | 0 => fun H => H ord0
  | n'.+1 => fun H =>
      tensor_product (H ord0) (@tensor_product_family n' (fun i => H (lift ord0 i)))
  end.

(** ** Statement *)

Definition AX_direct_product_multipartite_independence_equals_irredundance : Prop :=
  forall (n : nat) (H : 'I_n.+1 -> sgraph),
    (forall i : 'I_n.+1, is_complete_multipartite (H i)) ->
    α([set: tensor_product_family H]) = IR (tensor_product_family H).
