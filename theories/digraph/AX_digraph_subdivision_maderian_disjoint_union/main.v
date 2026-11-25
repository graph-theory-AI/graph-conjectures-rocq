(** * Disjoint unions of δ⁺-maderian digraphs

Aboulker, Cohen, Havet, Lochet, Moura, Thomassé, "Subdivisions in digraphs of large out-degree or
large dichromatic number", 2016, arXiv:1610.00876, Conjecture 7 (1610.00876__02).

A subdivision of a digraph F is obtained by replacing the arcs of F by directed paths (internally
disjoint, with new internal vertices).  A digraph F is δ⁺-maderian if there is an integer m such
that every digraph of minimum out-degree at least m contains a subdivision of F.

Conjecture: if F_1 and F_2 are δ⁺-maderian, then the disjoint union of F_1 and F_2 is δ⁺-maderian.

Encoding.  Digraphs are those of GraphTheory ([diGraph]: a finite type of vertices with a boolean
relation [--]).  Digons are allowed, as in the source.  Loops are allowed too; this is equivalent,
as a digraph with a loop has no subdivision here, hence is not δ⁺-maderian, and the loops of the
other digraphs change their out-degrees by at most one.  The digraphs whose minimum out-degree is
considered have at least one vertex. *)

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

(** Out-degree. *)
Definition outdeg (D : diGraph) (v : D) : nat := #|N(v)|.

(** The minimum out-degree of [D] is at least [k]. *)
Definition min_outdeg_ge (D : diGraph) (k : nat) : Prop := forall v : D, (k <= outdeg v)%N.

(** Disjoint union. *)
Definition digraph_sum (D1 D2 : diGraph) : diGraph :=
  DiGraph (fun x y : D1 + D2 =>
    match x, y with
    | inl a, inl b => a -- b
    | inr a, inr b => a -- b
    | _, _ => false
    end).

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

Definition AX_digraph_subdivision_maderian_disjoint_union : Prop :=
  forall F1 F2 : diGraph,
    delta_plus_maderian F1 -> delta_plus_maderian F2 ->
    delta_plus_maderian (digraph_sum F1 F2).
