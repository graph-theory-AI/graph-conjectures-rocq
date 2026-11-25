(** * Induced paths uniquely covered by stable sets

Scott, Seymour, "Induced subgraphs of graphs with large chromatic number. IX. Rainbow paths",
arXiv:1702.01094, concluding question (1702.01094__01).

A set of vertices is stable if its elements are pairwise nonadjacent.

Question: let G be a triangle-free graph with very large chromatic number (in terms of s), and let
𝒜 be a set of stable subsets, not necessarily pairwise disjoint, of V(G) with union V(G).  Does
there necessarily exist an s-vertex induced path P of G such that for each vertex v of P, some
X ∈ 𝒜 satisfies X ∩ V(P) = {v}?

The proposition states the positive answer.

Encoding.  Graphs are finite and simple.  𝒜 is a family (A i) indexed by a finite type. *)

From GraphTheory Require Import digraph sgraph dom coloring.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

Section Sequences.
Variable T : finType.
Implicit Types s : seq T.

(** The list of the pairs of consecutive elements of [s]: the edges of a walk. *)
Definition seq_edge_list s : seq {set T} :=
  map (fun e : T * T => [set e.1; e.2]) (zip s (behead s)).

End Sequences.

Section InducedPathsCycles.
Variable G : sgraph.
Implicit Types (p : seq G) (u v : G).

(** [p] is an induced path (possibly empty): adjacent vertices of [p] are consecutive. *)
Definition chordless_path p : Prop :=
  [/\ uniq p, sorted (--) p
    & forall u v : G, u \in p -> v \in p -> u -- v -> [set u; v] \in seq_edge_list p].

End InducedPathsCycles.

(** [G] has no triangle. *)
Definition triangle_free (G : sgraph) : Prop :=
  forall x y z : G, x -- y -> y -- z -> z -- x -> False.

(** ** Statement *)

Definition AX_large_chromatic_induced_path_uniquely_covered : Prop :=
  forall s : nat, exists n : nat,
    forall (G : sgraph) (I : finType) (A : I -> {set G}),
      triangle_free G ->
      n <= χ([set: G]) ->
      (forall i : I, stable (A i)) ->
      (forall v : G, exists i : I, v \in A i) ->
      exists p : seq G,
        [/\ size p = s,
            chordless_path p
          & forall v : G, v \in p -> exists i : I, A i :&: [set:: p] = [set v]].
