(** * Erdős-Pósa property for long directed cycles

Havet, Maia, "On disjoint directed cycles with prescribed minimum lengths", INRIA Research Report
RR-8286 (2013); Open Problem Garden, erdos_posa_property_for_long_directed_cycles.

Conjecture: let l >= 2.  For every integer n >= 0, there exists an integer t = t_n(l) such that
every digraph D either has n pairwise vertex-disjoint directed cycles of length at least l, or has a
set T of at most t vertices such that D - T has no directed cycle of length at least l.

Encoding.  Digraphs are those of GraphTheory ([diGraph]): a finite type of vertices with a boolean
relation [--].  Digons are allowed, and so are loops, which play no role here as l >= 2.  A directed
cycle is given by the sequence of its vertices.  Those of D - T are those of D that avoid T. *)

From GraphTheory Require Import digraph.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/digraph.v *)

(** The vertices [c] form a directed cycle, of length [size c] (a loop or a digon is one). *)
Definition dicycle (D : diGraph) (c : seq D) : bool := ~~ nilp c && ucycleb (--) c.

(** ** Statement *)

Definition OPG_erdos_posa_long_directed_cycles : Prop :=
  forall l n : nat, 2 <= l ->
    exists t : nat, forall D : diGraph,
      (exists C : 'I_n -> seq D,
         (forall i : 'I_n, dicycle (C i) /\ l <= size (C i)) /\
         (forall i j : 'I_n, i != j -> [disjoint C i & C j])) \/
      (exists T : {set D}, #|T| <= t /\
         forall c : seq D, dicycle c -> l <= size c -> exists2 v : D, v \in T & v \in c).
