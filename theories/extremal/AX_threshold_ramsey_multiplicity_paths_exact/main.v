(** * Threshold Ramsey multiplicity of paths

Conlon, Fox, Sudakov, Wei, "Threshold Ramsey multiplicity for paths and even cycles",
arXiv:2108.00991, Conjecture 3 (2108.00991__00).

P_k is the path on k vertices.  The Ramsey number r(H) is the minimum n such that every
2-colouring of the edges of K_n has a monochromatic copy of H, and the threshold Ramsey
multiplicity m(H) is the minimum number of monochromatic copies of H in a 2-colouring of the edges
of K_r(H).

Conjecture 3: for k sufficiently large, m(P_k) = k!/2 if k is even, and m(P_k) = (k-1)(k-1)!/4 if
k is odd.

Encoding.  A copy of H is a subgraph isomorphic to H, not necessarily induced.  The number of
copies is the number of injective homomorphisms divided by the number of automorphisms of H (the
division is exact).  A 2-colouring of the edges of K_n is given by the graph G formed by the edges
of the first colour, and its complement (the Ramsey number is defined for any number of colours,
hence with functions).  "m(H) = m" is a relation between H and m. *)

From GraphTheory Require Import preliminaries digraph sgraph.
From mathcomp Require Import boot perm.

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

(** The path on [n] vertices. *)
Definition path_graph (n : nat) : sgraph := sgraph_of_rel (fun i j : 'I_n => (val i).+1 == val j).

(** ** Definitions copied from GraphLib/chromatic.v *)

(** The spanning subgraph formed by the edges with colour in [p]. *)
Definition edge_color_class (G : sgraph) (C : eqType) (col : {set G} -> C) (p : pred C) : sgraph :=
  del_edge_set [set e : {set G} | ~~ p (col e)].

(** ** Definitions copied from GraphLib/digraph.v *)

(** The automorphisms of [D]. *)
Definition automorphisms (D : diGraph) : {set {perm D}} :=
  [set p : {perm D} | [forall u : D, [forall v : D, (p u -- p v) == (u -- v)]]].

(** ** Definitions copied from GraphLib/extremal.v *)

(** [Host] arrows the family [Fam] with [k] colours: each colouring of its edges with [k]
    colours has a monochromatic copy of a graph of [Fam]. *)
Definition ramsey_arrows (Host : sgraph) (k r : nat) (Fam : 'I_r -> sgraph) : Prop :=
  forall col : {set Host} -> 'I_k,
    exists (i : 'I_r) (c : 'I_k), subgraph (Fam i) (edge_color_class col (pred1 c)).

(** The Ramsey number of the family [Fam] with [k] colours is [n]. *)
Definition ramsey_number (k r : nat) (Fam : 'I_r -> sgraph) (n : nat) : Prop :=
  ramsey_arrows 'K_n k Fam /\ forall m : nat, m < n -> ~ ramsey_arrows 'K_m k Fam.

(** The injective homomorphisms from [H] to [G]. *)
Definition injective_homs (H G : sgraph) : {set {ffun H -> G}} :=
  [set f : {ffun H -> G} |
    injectiveb f & [forall x : H, [forall y : H, (x -- y) ==> (f x -- f y)]]].

(** The number of copies of [H] in [G], as subgraphs. *)
Definition copy_count (H G : sgraph) : nat :=
  #|injective_homs H G| %/ #|automorphisms H|.

(** The number of copies of [H] in [G] and in its complement. *)
Definition mono_copy_count (H G : sgraph) : nat := copy_count H G + copy_count H (compl G).

(** The threshold Ramsey multiplicity of [H] is [m]: the minimum number of monochromatic copies
    of [H] in a 2-colouring of the edges of a complete graph whose number of vertices is the
    Ramsey number of [H] with 2 colours. *)
Definition threshold_multiplicity (H : sgraph) (m : nat) : Prop :=
  exists R : nat, [/\ ramsey_number 2 (fun _ : 'I_1 => H) R,
    forall G : sgraph, #|G| = R -> m <= mono_copy_count H G
  & exists2 G : sgraph, #|G| = R & mono_copy_count H G = m].

(** ** Statement *)

Definition AX_threshold_ramsey_multiplicity_paths_exact : Prop :=
  exists K : nat, forall k : nat, K <= k ->
    exists2 m : nat, threshold_multiplicity (path_graph k) m &
      (if odd k then 4 * m = k.-1 * (k.-1)`! else 2 * m = k`!).
