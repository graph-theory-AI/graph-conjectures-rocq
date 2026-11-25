(** * Ramsey numbers of arbitrary growth

Ahme, Scott, "Graphs with arbitrary Ramsey number and connectivity", arXiv:2311.01887,
Conjecture 10 (2311.01887__00).

The Ramsey number r(G) of a graph G is the minimum N such that every 2-colouring of the edges of
K_N has a monochromatic copy of G.

Conjecture 10: for every function f from the natural numbers to themselves with
n <= f(n) <= r(K_n) for all n, and for every ε > 0, there is a sequence of graphs (G_n) such that
|V(G_n)| = n and (1-ε) f(n) <= r(G_n) <= (1+ε) f(n) for all sufficiently large n.

Encoding.  ε is a rational number, which is equivalent.  "r(G) = R" is a relation between G and R,
and r(G_n) exists according to the statement.  The copies are not necessarily induced.  The Ramsey
number is defined for any number of colours and any family of graphs, hence with functions. *)

From GraphTheory Require Import digraph sgraph.
From mathcomp Require Import boot algebra.

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

(** ** Statement *)

Definition AX_ramsey_number_arbitrary_growth_rate_approximation : Prop :=
  forall f : nat -> nat,
    (forall n R : nat, ramsey_number 2 (fun _ : 'I_1 => 'K_n) R -> n <= f n <= R) ->
    forall eps : rat, (0 < eps)%R ->
      exists2 Gs : nat -> sgraph, (forall n : nat, #|Gs n| = n) &
        exists N : nat, forall n : nat, N <= n ->
          exists2 R : nat, ramsey_number 2 (fun _ : 'I_1 => Gs n) R &
            ((1 - eps) * (f n)%:R <= R%:R)%R /\ (R%:R <= (1 + eps) * (f n)%:R)%R.
