(** * Bermond-Thomassen conjecture

Bermond, Thomassen, "Cycles in digraphs - a survey", J. Graph Theory 5 (1981); Open Problem Garden,
the_bermond_thomassen_conjecture.

Conjecture: for every positive integer k, every digraph with minimum out-degree at least 2k-1
contains k pairwise vertex-disjoint directed cycles.

Encoding.  Digraphs are those of GraphTheory ([diGraph]): a finite type of vertices with a boolean
relation [--].  Digons are allowed, and the digraph is nonempty.  Loops are allowed too, which
changes nothing: if fewer than k vertices have a loop, say m, their deletion leaves a nonempty
digraph of minimum out-degree at least 2k-1-m >= 2(k-m)-1.  The trivial case k = 0 is included. *)

From GraphTheory Require Import digraph.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/digraph.v *)

(** Out-degree. *)
Definition outdeg (D : diGraph) (v : D) : nat := #|N(v)|.

(** The minimum out-degree of [D] is at least [k]. *)
Definition min_outdeg_ge (D : diGraph) (k : nat) : Prop := forall v : D, (k <= outdeg v)%N.

(** The vertices [c] form a directed cycle, of length [size c] (a loop or a digon is one). *)
Definition dicycle (D : diGraph) (c : seq D) : bool := ~~ nilp c && ucycleb (--) c.

(** ** Statement *)

Definition OPG_bermond_thomassen_outdegree_disjoint_cycles : Prop :=
  forall (D : diGraph) (k : nat), 0 < #|D| -> min_outdeg_ge D (2 * k - 1) ->
    exists C : 'I_k -> seq D,
      (forall i : 'I_k, dicycle (C i)) /\
      (forall i j : 'I_k, i != j -> [disjoint C i & C j]).
