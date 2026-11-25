(** * Subdivisions of transitive tournaments in digraphs of large semidegree

Aboulker, Cohen, Havet, Lochet, Moura, Thomassé, "Subdivisions in digraphs of large out-degree or
large dichromatic number", 2016, arXiv:1610.00876, Conjecture 3 (1610.00876__00).

A subdivision of a digraph F is obtained by replacing the arcs of F by directed paths (internally
disjoint, with new internal vertices).  TT_k is the transitive tournament on k vertices, and
δ⁰(D) is the minimum of the in-degrees and out-degrees of the vertices of D.

Conjecture: for every k, there exists a least integer m such that every digraph D with
δ⁰(D) >= m contains a subdivision of TT_k.

Encoding.  Digraphs are those of GraphTheory ([diGraph]: a finite type of vertices with a boolean
relation [--]).  D has at least one vertex, otherwise its minimum semidegree is undefined.  The
word "least" is omitted: there is a least such integer as soon as there is one.  Digons are
allowed.  Loops are allowed too; this is equivalent, as they change the degrees by at most one and
are not used by a subdivision of TT_k. *)

From GraphTheory Require Import digraph.
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

(** In-degree. *)
Definition indeg (D : diGraph) (v : D) : nat := #|[set u | u -- v]|.

(** The minimum in-degree and the minimum out-degree of [D] are at least [k]. *)
Definition min_semidegree_ge (D : diGraph) (k : nat) : Prop :=
  forall v : D, (k <= outdeg v)%N /\ (k <= indeg v)%N.

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

(** ** Statement *)

Definition AX_outdegree_transitive_tournament_subdivision_semidegree : Prop :=
  forall k : nat, exists m : nat, forall D : diGraph,
    0 < #|D| -> min_semidegree_ge D m ->
    contains_disubdivision (transitive_tournament k) D.
