(** * Subdivisions of transitive tournaments in digraphs of large out-degree

Mader; Open Problem Garden,
subdivision_of_a_transitive_tournament_in_digraphs_with_large_outdegree.

A subdivision of a digraph F is obtained by replacing the arcs uv of F by directed paths from u
to v with pairwise disjoint interiors.

Conjecture: for all k, there is an integer f(k) such that every digraph of minimum out-degree at
least f(k) contains a subdivision of the transitive tournament of order k.

Encoding.  Digraphs are those of GraphTheory ([diGraph]): a finite type of vertices with a boolean
relation [--].  They are nonempty, and may have digons.  Loops are allowed, which changes nothing:
they increase the out-degrees by at most 1, and are not used by subdivisions of loopless
digraphs. *)

From GraphTheory Require Import preliminaries digraph.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

Section Sequences.
Variable T : finType.
Implicit Types (s : seq T) (x y : T).

(** The elements of [s] other than [x] and [y]. *)
Definition seq_interior x y s : {set T} := [set:: s] :\: [set x; y].

End Sequences.

(** ** Definitions copied from GraphLib/digraph.v *)

(** The transitive tournament on [n] vertices. *)
Definition transitive_tournament (n : nat) : diGraph := DiGraph [rel u v : 'I_n | u < v].

(** Out-degree. *)
Definition outdeg (D : diGraph) (v : D) : nat := #|N(v)|.

(** The minimum out-degree of [D] is at least [k]. *)
Definition min_outdeg_ge (D : diGraph) (k : nat) : Prop := forall v : D, (k <= outdeg v)%N.

(** [D] contains a subdivision of [F]: distinct branch vertices, and, for each arc of [F], a
    directed path between the corresponding branch vertices; the interiors of these paths are
    pairwise disjoint and contain no branch vertex. *)
Definition contains_disubdivision (F D : diGraph) : Prop :=
  exists branch : F -> D,
    injective branch /\
    exists paths : F -> F -> seq D,
      (forall u v : F, u -- v ->
        [/\ (0 < size (paths u v))%N,
            upath (branch u) (branch v) (paths u v)
          & [disjoint seq_interior (branch u) (branch v) (branch u :: paths u v)
             & [set y | [exists x : F, branch x == y]]]]) /\
      (forall u v x y : F, u -- v -> x -- y ->
        ((u != x) || (v != y)) ->
        [disjoint seq_interior (branch u) (branch v) (branch u :: paths u v)
         & seq_interior (branch x) (branch y) (branch x :: paths x y)]).

(** [F] is δ⁺-maderian: the digraphs of large minimum out-degree contain a subdivision of [F]. *)
Definition delta_plus_maderian (F : diGraph) : Prop :=
  exists m : nat, forall D : diGraph, (0 < #|D|)%N ->
    min_outdeg_ge D m -> contains_disubdivision F D.

(** ** Statement *)

Definition OPG_outdegree_transitive_tournament_subdivision : Prop :=
  forall k : nat, delta_plus_maderian (transitive_tournament k).
