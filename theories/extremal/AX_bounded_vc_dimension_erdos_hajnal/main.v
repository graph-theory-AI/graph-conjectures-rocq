(** * Erdős-Hajnal conjecture for graphs of bounded VC-dimension

Fox, Pach, Suk, "Bounded VC-dimension implies the Schur-Erdős conjecture", arXiv:1912.02342,
Conjecture 4.1 (1912.02342__00).

A set S of vertices is shattered if every subset of S is N(v) ∩ S for some vertex v, where N(v) is
the (open) neighbourhood of v.  The VC-dimension of a graph is the maximum size of a shattered
set.

Conjecture 4.1: for every d >= 2, there is a constant ε(d) > 0 such that every graph on n vertices
with VC-dimension at most d has a clique or a stable set of size at least n^ε(d).

Encoding.  ε(d) is of the form 1/q, where q is a positive integer.  This is equivalent, as ε(d)
can be decreased. *)

From GraphTheory Require Import digraph sgraph dom.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/extremal.v *)

(** The set [S] is shattered by the neighbourhoods of the vertices. *)
Definition shattered (G : sgraph) (S : {set G}) : Prop :=
  forall T : {set G}, T \subset S -> exists v : G, N(v) :&: S = T.

(** The VC-dimension of [G] is at most [d]. *)
Definition vc_dim_le (G : sgraph) (d : nat) : Prop :=
  forall S : {set G}, shattered S -> #|S| <= d.

(** ** Statement *)

Definition AX_bounded_vc_dimension_erdos_hajnal : Prop :=
  forall d : nat, 2 <= d ->
    exists q : nat,
      0 < q /\
      forall G : sgraph,
        vc_dim_le G d ->
        exists S : {set G}, (cliqueb S || stable S) /\ #|G| <= #|S| ^ q.
