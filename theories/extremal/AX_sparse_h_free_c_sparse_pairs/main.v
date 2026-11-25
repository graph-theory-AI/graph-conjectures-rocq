(** * Sparse pairs in sparse H-free graphs

Chudnovsky, Fox, Scott, Seymour, Spirkl, "Sparse graphs with no polynomial-sized anticomplete
pairs", arXiv:1810.00058, Conjecture 3.4 (1810.00058__02).

A graph G is H-free if it has no induced subgraph isomorphic to H, and ε-bounded if |N[v]| < ε|G|
for every vertex v, where |G| is the number of vertices and N[v] is the closed neighbourhood.  A
c-sparse (x,y)-pair consists of two disjoint sets A and B of vertices with at most c|A||B| edges
between them, such that |A| >= x and |B| >= y.

Conjecture 3.4: for every graph H, there are ε, s > 0 such that every H-free ε-bounded graph G
with |G| > 1 has a c-sparse (εc^s|G|, ε|G|)-pair for every c with 0 <= c <= 1.

Encoding.  ε and c are rational numbers p/d and a/b with p <= d and a <= b, s is a positive
integer, and the inequalities are multiplied by the denominators.  This is equivalent: ε can be
decreased and s can be increased, and the case of a real number c follows from its rational
approximations (there are finitely many pairs for each G). *)

From GraphTheory Require Import digraph sgraph.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

(** The number of pairs [(a, b)] of adjacent vertices with [a] in [A] and [b] in [B] (an edge
    with both ends in both sets is counted twice). *)
Definition edge_count_between (G : sgraph) (A B : {set G}) : nat :=
  #|[set p : G * G | [&& p.1 \in A, p.2 \in B & p.1 -- p.2]]|.

(** [G] has an induced subgraph isomorphic to [H]. *)
Definition has_induced_copy (G H : sgraph) : Prop := inhabited (H ⇀ G).

(** [G] has no induced subgraph isomorphic to [H]. *)
Definition induced_free (G H : sgraph) : Prop := ~ has_induced_copy G H.

(** ** Definitions copied from GraphLib/extremal.v *)

(** [G] is [p/d]-bounded: the closed neighbourhoods have less than [(p / d) |G|] vertices. *)
Definition eps_bounded (G : sgraph) (p d : nat) : Prop :=
  forall v : G, d * #|N[v]| < p * #|G|.

(** The disjoint sets [A] and [B] have density at most [a / b]. *)
Definition sparse_pair (G : sgraph) (A B : {set G}) (a b : nat) : Prop :=
  [disjoint A & B] /\
  b * edge_count_between A B <= a * (#|A| * #|B|).

(** ** Statement *)

Definition AX_sparse_h_free_c_sparse_pairs : Prop :=
  forall H : sgraph,
    exists p d s : nat,
      [/\ 0 < p, p <= d, 0 < s &
          forall G : sgraph,
            1 < #|G| ->
            induced_free G H ->
            eps_bounded G p d ->
            forall a b : nat, 0 < b -> a <= b ->
              exists A B : {set G},
                [/\ sparse_pair A B a b,
                    a ^ s * (p * #|G|) <= d * (b ^ s * #|A|) &
                    p * #|G| <= d * #|B|]].
