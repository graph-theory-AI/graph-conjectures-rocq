(** * Pure pairs with one linear side when a sparse graph is excluded

Scott, Seymour, Spirkl, "Pure pairs. VIII. Excluding a sparse graph", arXiv:2201.04062,
Possibility 1.6 (2201.04062__00).

A graph G is H-free if it has no induced subgraph isomorphic to H, and |G| is the number of its
vertices.  A pure pair of G is a pair A, B of disjoint sets of vertices that are complete (every
vertex of A is adjacent to every vertex of B) or anticomplete (no edge between A and B).  The
congestion of a graph H is the maximum of 1 - (|J| - 1) / |E(J)| over the subgraphs J of H with at
least one edge (0 if H has no edge).

Question: is it true that, for all c > 0, there exists ξ > 0 such that, for every graph H with
congestion at most ξ, there exists ε > 0 such that every graph G with |G| > 1 that is both H-free
and (complement of H)-free has a pure pair A, B with |A| >= ε|G| and |B| >= ε|G|^(1-c)?

The proposition states that the answer is yes.

Encoding.  Graphs are finite and simple.  The constants are c = 1/k, ξ = 1/q and ε = 1/m, without
loss of generality as |G| > 1: c, ξ and ε can be decreased.  The inequality |B| >= ε|G|^(1-c) is
raised to the power k and becomes |G|^(k-1) <= (m|B|)^k. *)

From GraphTheory Require Import digraph sgraph.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

(** [A] and [B] are disjoint and there is no edge between them. *)
Definition anticomplete (G : sgraph) (A B : {set G}) : bool :=
  [disjoint A & B] && ~~ neighbor A B.

(** Every vertex of [A] is adjacent to every vertex of [B]. *)
Definition complete_between (G : sgraph) (A B : {set G}) : bool :=
  [forall a in A, [forall b in B, a -- b]].

(** [G] has an induced subgraph isomorphic to [H]. *)
Definition has_induced_copy (G H : sgraph) : Prop := inhabited (H ⇀ G).

(** [G] has no induced subgraph isomorphic to [H]. *)
Definition induced_free (G H : sgraph) : Prop := ~ has_induced_copy G H.

(** ** Definitions specific to the conjecture *)

(** The congestion of [H] is at most [1 / q]: for each subgraph of [H], with vertex set [S] and
    nonempty edge set [F], 1 - (|S| - 1) / |F| is at most [1 / q]. *)
Definition congestion_le (H : sgraph) (q : nat) : Prop :=
  forall (S : {set H}) (F : {set {set H}}),
    F \subset E(H) -> (forall e : {set H}, e \in F -> e \subset S) -> 0 < #|F| ->
    q * #|F| <= q * (#|S| - 1) + #|F|.

(** ** Statement *)

Definition AX_pure_pairs_sparse_excluded_linear_side : Prop :=
  forall k : nat, 0 < k -> exists q : nat, 0 < q /\
    forall H : sgraph, congestion_le H q -> exists m : nat, 0 < m /\
      forall G : sgraph, 1 < #|G| -> induced_free G H -> induced_free G (compl H) ->
        exists A B : {set G},
          [/\ [disjoint A & B], complete_between A B || anticomplete A B,
              #|G| <= m * #|A| & #|G| ^ (k - 1) <= (m * #|B|) ^ k].
