(** * Anticomplete pairs with one linear side in sparse H-free graphs

Chudnovsky, Fox, Scott, Seymour, Spirkl, "Sparse graphs with no polynomial-sized anticomplete
pairs", arXiv:1810.00058, Conjecture 1.4 (1810.00058__00).

A graph G is H-free if it has no induced subgraph isomorphic to H, and ε-bounded if
|N[v]| < ε|G| for every vertex v, where |G| is the number of vertices and N[v] is the closed
neighbourhood.  An anticomplete (x,y)-pair consists of two disjoint sets A and B of vertices with
no edge between them, such that |A| >= x and |B| >= y.

Conjecture 1.4: for every graph H, there is ε > 0 such that every H-free ε-bounded graph G with
|G| > 1 has an anticomplete (ε|G|^ε, ε|G|)-pair.

Encoding.  Graphs are finite and simple.  ε is a rational number p/d with p <= d.  This is
equivalent, as ε can be decreased.  The inequality |A| >= ε|G|^ε is raised to the power d, and
multiplied by d^d. *)

From GraphTheory Require Import digraph sgraph.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

(** [A] and [B] are disjoint and there is no edge between them. *)
Definition anticomplete (G : sgraph) (A B : {set G}) : bool :=
  [disjoint A & B] && ~~ neighbor A B.

(** [G] has an induced subgraph isomorphic to [H]. *)
Definition has_induced_copy (G H : sgraph) : Prop := inhabited (H ⇀ G).

(** [G] has no induced subgraph isomorphic to [H]. *)
Definition induced_free (G H : sgraph) : Prop := ~ has_induced_copy G H.

(** ** Definitions copied from GraphLib/extremal.v *)

(** [G] is [p/d]-bounded: the closed neighbourhoods have less than [(p / d) |G|] vertices. *)
Definition eps_bounded (G : sgraph) (p d : nat) : Prop :=
  forall v : G, d * #|N[v]| < p * #|G|.

(** ** Statement *)

Definition AX_sparse_h_free_anticomplete_pairs_linear : Prop :=
  forall H : sgraph, exists p d : nat,
    [/\ 0 < p, p <= d &
        forall G : sgraph, 1 < #|G| -> induced_free G H -> eps_bounded G p d ->
          exists A B : {set G},
            [/\ anticomplete A B,
                p ^ d * #|G| ^ p <= d ^ d * #|A| ^ d &
                p * #|G| <= d * #|B|]].
