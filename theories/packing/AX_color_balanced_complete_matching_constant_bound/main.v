(** * Almost colour-balanced perfect matchings of complete graphs

Hogan, Scott, Tsarev, "Colour-balanced subgraphs", arXiv:2604.09449, Conjecture 6.2
(2604.09449__01).

A k-edge-colouring of a graph, not necessarily proper, is colour-balanced if all colour classes have
the same size.  Let c be a colour-balanced k-edge-colouring of K_{2kt}.  For a perfect matching M,
which has kt edges, let f_c(M) be the sum over the k colours i of | m_i - t |, where m_i is the
number of edges of M of colour i.

Conjecture: there is an absolute constant C such that, for all positive integers k and t, every
colour-balanced k-edge-colouring c of K_{2kt} admits a perfect matching M with f_c(M) < C.

Encoding.  A colouring is a function on all sets of vertices, whose values outside the edges are
irrelevant.  The constant C is an integer, without loss of generality.  The absolute value is
written with two truncated subtractions, one of which is zero. *)

From GraphTheory Require Import digraph sgraph connectivity.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/packing.v *)

(** [M] is a perfect matching. *)
Definition perfect_matching (G : sgraph) (M : {set {set G}}) : Prop :=
  matching M /\ cover M = [set: G].

(** ** Definitions specific to the conjecture *)

(** The edges of [F] with colour [i]. *)
Definition color_class (G : sgraph) (k : nat) (c : {set G} -> 'I_k) (F : {set {set G}})
    (i : 'I_k) : {set {set G}} :=
  [set e in F | c e == i].

(** The colouring [c] is colour-balanced. *)
Definition color_balanced (G : sgraph) (k : nat) (c : {set G} -> 'I_k) : Prop :=
  forall i j : 'I_k, #|color_class c E(G) i| = #|color_class c E(G) j|.

(** f_c(M). *)
Definition imbalance (G : sgraph) (k t : nat) (c : {set G} -> 'I_k) (M : {set {set G}}) : nat :=
  \sum_(i < k) ((#|color_class c M i| - t) + (t - #|color_class c M i|)).

(** ** Statement *)

Definition AX_color_balanced_complete_matching_constant_bound : Prop :=
  exists C : nat, forall k t : nat, 0 < k -> 0 < t ->
    forall c : {set 'K_(2 * k * t)} -> 'I_k,
      color_balanced c ->
      exists M : {set {set 'K_(2 * k * t)}}, perfect_matching M /\ imbalance t c M < C.
