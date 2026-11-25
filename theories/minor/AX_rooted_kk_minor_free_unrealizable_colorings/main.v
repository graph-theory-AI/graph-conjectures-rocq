(** * Sets of colourings that rooted-K_k-minor-free graphs do not realize

Dvořák, Swart, "A note on extendable sets of colorings and rooted minors", arXiv:2504.07764,
Conjecture 4 (2504.07764__00).

A set of k-colourings of a set X is a set C of functions f : X -> [k] closed under the
permutations of the colours: if f ∈ C then π ∘ f ∈ C for every permutation π of [k].  A graph G
realizes C if X ⊆ V(G) and, for every f : X -> [k], f ∈ C if and only if f extends to a proper
k-colouring of G.  For X ⊆ V(G), H is an X-rooted minor of G if it has a model in G where every
branch set contains a vertex of X; otherwise, G is X-rooted-H-minor-free.

Conjecture 4: for every integer k >= 3, there are a set X and a set C of k-colourings of X such
that no X-rooted-K_k-minor-free graph G realizes C.

Encoding.  Graphs are finite and simple.  The set X, which is chosen before G, is ['I_n], and an
injective map from ['I_n] to the vertices of G gives its place in G. *)

From GraphTheory Require Import digraph sgraph coloring minor.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/chromatic.v *)

(** [col] is a proper colouring of [G]. *)
Definition proper_coloring (G : sgraph) (C : finType) (col : G -> C) : bool :=
  coloring (preim_partition col [set: G]) [set: G].

(** ** Definitions specific to the conjecture *)

(** [C] is closed under the permutations of the colours. *)
Definition closed_under_permutations (n k : nat) (C : {set {ffun 'I_n -> 'I_k}}) : Prop :=
  forall (pi : 'I_k -> 'I_k) (f : {ffun 'I_n -> 'I_k}),
    bijective pi -> f \in C -> [ffun j => pi (f j)] \in C.

(** [H] is a minor of [G] rooted at the image of [x]. *)
Definition rooted_minor (n : nat) (G H : sgraph) (x : 'I_n -> G) : Prop :=
  exists phi : H -> {set G},
    minor_rmap phi /\ (forall i, phi i :&: [set x j | j in 'I_n] != set0).

(** [G] realizes [C] on the image of [x]: the elements of [C] are the colourings that extend to
    a proper colouring of [G]. *)
Definition realizes (n k : nat) (G : sgraph) (x : 'I_n -> G)
    (C : {set {ffun 'I_n -> 'I_k}}) : Prop :=
  forall f : {ffun 'I_n -> 'I_k},
    f \in C <-> exists2 col : G -> 'I_k, proper_coloring col & forall j, col (x j) = f j.

(** ** Statement *)

Definition AX_rooted_kk_minor_free_unrealizable_colorings : Prop :=
  forall k : nat, 3 <= k ->
    exists (n : nat) (C : {set {ffun 'I_n -> 'I_k}}),
      closed_under_permutations C /\
      forall (G : sgraph) (x : 'I_n -> G),
        injective x -> ~ rooted_minor 'K_k x -> ~ realizes x C.
