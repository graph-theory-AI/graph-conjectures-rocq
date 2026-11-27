(** * Subdivisions in digraphs of large strong connectivity

Aboulker, Cohen, Havet, Lochet, Moura, Thomassé, "Subdivisions in digraphs of large out-degree or
large dichromatic number", 2016, arXiv:1610.00876, Problem 16 (1610.00876__05).

A subdivision of a digraph F is obtained by replacing the arcs of F by directed paths (internally
disjoint, with new internal vertices).  For a digraph parameter γ, a digraph F is γ-maderian if
there is an integer m such that every digraph D with γ(D) >= m contains a subdivision of F.  The
strong connectivity κ(D) is the least number of vertices whose removal leaves a digraph that is not
strongly connected, and κ'(D) is the strong arc-connectivity (the same for arcs).

Question: are all digraphs κ-maderian?  Are they all κ'-maderian?

Proxy (weaker).  The proposition states the positive answer to the first question only, which the
canonical name designates.  According to a note of the source, the second question has a negative
answer (Gishboliner, Steiner, Szabó, arXiv:2008.13224, Propositions 10-11).

Encoding.  Digraphs are those of GraphTheory ([diGraph]: a finite type of vertices with a boolean
relation [--]).  Digons are allowed, as in the source.  F has no loop; loops are allowed in D, where
they are irrelevant.  "κ(D) >= k" means that D is k-strong, which requires more than k vertices. *)

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

(** [D] is strongly connected. *)
Definition strongly_connected (D : diGraph) : bool :=
  [forall x : D, forall y : D, connect (--) x y].

(** [D] is [k]-strong: it has more than [k] vertices, and it remains strongly connected when
    fewer than [k] vertices are deleted. *)
Definition kstrong (D : diGraph) (k : nat) : bool :=
  (k < #|D|) && [forall S : {set D}, (#|S| < k) ==> strongly_connected (induced (~: S))].

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

(** ** Definitions specific to the conjecture *)

(** [F] is κ-maderian. *)
Definition kappa_maderian (F : diGraph) : Prop :=
  exists k : nat, forall D : diGraph, kstrong D k -> contains_disubdivision F D.

(** ** Statement *)

Definition proxy_AX_digraph_subdivision_strong_connectivity_maderian : Prop :=
  forall F : diGraph, irreflexive (@edge_rel F) -> kappa_maderian F.
