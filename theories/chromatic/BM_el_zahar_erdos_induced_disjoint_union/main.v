(** * The El-Zahar–Erdős conjecture

El-Zahar, Erdős; Bondy, Murty, "Graph Theory", Appendix A, problem 46.

A graph is k-chromatic if its chromatic number is k.

Question: does there exist a function f such that every graph of chromatic number at least f(r, k)
contains either an r-clique or an induced subgraph which is the disjoint union of two k-chromatic
graphs?

The proposition states the positive answer.

Encoding.  Graphs are finite and simple.  The two k-chromatic graphs are induced by disjoint sets A
and B of vertices, with no edge between A and B. *)

From GraphTheory Require Import digraph sgraph dom coloring.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

(** [A] and [B] are disjoint and there is no edge between them. *)
Definition anticomplete (G : sgraph) (A B : {set G}) : bool :=
  [disjoint A & B] && ~~ neighbor A B.

(** ** Statement *)

Definition BM_el_zahar_erdos_induced_disjoint_union : Prop :=
  exists f : nat -> nat -> nat,
    forall (r k : nat) (G : sgraph),
      f r k <= χ([set: G]) ->
      (exists S : {set G}, clique S /\ #|S| = r) \/
      (exists A B : {set G}, [/\ anticomplete A B, χ(A) = k & χ(B) = k]).
