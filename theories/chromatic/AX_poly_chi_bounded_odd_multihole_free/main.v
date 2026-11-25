(** * Excluding disjoint odd holes

Chudnovsky, Scott, Seymour, Spirkl, "Polynomial bounds for chromatic number. VII. Disjoint holes",
arXiv:2202.09118, introduction (2202.09118__01).

A k-multihole of G is an induced subgraph with k components, all of them cycles of length at least
4.  A class of graphs is polynomially χ-bounded if there is a polynomial f such that χ(G) <= f(ω(G))
for every graph G of the class.

Question: is it true that, for every k >= 1, the class of the graphs with no k-multihole whose
cycles all have odd length is polynomially χ-bounded?  The positive answer is stated.

Encoding.  A multihole is a family of k induced cycles of length at least 4 that are pairwise
disjoint and with no edge between two of them.  The polynomial f is of the form c x^d, which is not
a restriction. *)

From GraphTheory Require Import digraph sgraph coloring.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

Section Sequences.
Variable T : finType.
Implicit Types c : seq T.

(** The list of the pairs of consecutive elements of the cyclic sequence [c]: the edges of a
    closed walk. *)
Definition seq_cycle_edge_list c : seq {set T} :=
  map (fun p : T * T => [set p.1; p.2]) (zip c (rot 1 c)).

End Sequences.

Section Cycles.
Variables (T : eqType) (r : rel T).
Implicit Types c : seq T.

(** [c] is a cycle (without repetition, of length at least 3) of the relation [r]. *)
Definition seq_cycle c : bool := ucycleb r c && (2 < size c).

End Cycles.

Section InducedPathsCycles.
Variable G : sgraph.
Implicit Types (c : seq G) (u v : G).

(** Adjacent vertices of [c] are consecutive in the cyclic sequence [c]. *)
Definition cyclic_chordless c : Prop :=
  forall u v, u \in c -> v \in c -> u -- v -> [set u; v] \in seq_cycle_edge_list c.

(** [c] is an induced cycle (of length at least 3). *)
Definition chordless_cycle c : Prop := seq_cycle (--) c /\ cyclic_chordless c.

(** [c] is a hole: an induced cycle of length at least 4. *)
Definition hole c : Prop := chordless_cycle c /\ 3 < size c.

End InducedPathsCycles.
Arguments cyclic_chordless {G} c.
Arguments hole {G} c.

(** ** Definitions copied from GraphLib/chromatic.v *)

(** The class [F] is polynomially chi-bounded. *)
Definition poly_chi_bounded (F : sgraph -> Prop) : Prop :=
  exists c d : nat,
    forall G : sgraph, F G -> χ([set: G]) <= c * ω([set: G]) ^ d.

(** ** Definitions specific to the conjecture *)

(** [G] has a [k]-multihole whose cycles [c i] all have odd length. *)
Definition odd_multihole (G : sgraph) (k : nat) : Prop :=
  exists c : 'I_k -> seq G,
    (forall i : 'I_k, hole (c i) /\ odd (size (c i))) /\
    (forall (i j : 'I_k) (x y : G),
       i != j -> x \in c i -> y \in c j -> x != y /\ ~~ (x -- y)).

(** ** Statement *)

Definition AX_poly_chi_bounded_odd_multihole_free : Prop :=
  forall k : nat, 1 <= k -> poly_chi_bounded (fun G : sgraph => ~ odd_multihole G k).
