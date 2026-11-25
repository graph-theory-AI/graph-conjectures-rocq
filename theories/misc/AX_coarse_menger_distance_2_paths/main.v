(** * Coarse Menger conjecture for paths at distance 2

Nguyen, Scott, Seymour, "Asymptotic structure. IV. A counterexample to the weak coarse Menger
conjecture", arXiv:2508.14332, open case c = 2 of the coarse Menger conjecture
(2508.14332__00).

For sets S and T of vertices of a graph G, an S-T path is a path from a vertex of S to a vertex of
T.  Two paths are at distance at least c if every vertex of the first one is at distance at least
c from every vertex of the second one.

Conjecture (case c = 2): for every k >= 1 there is ℓ > 0 such that for every graph G and all
S, T ⊆ V(G), either there are k S-T paths pairwise at distance at least 2, or there is a set X of at
most k-1 vertices such that every S-T path contains a vertex within distance ℓ of some vertex of X.

Encoding.  Graphs are finite.  Paths may have a single vertex.  The last property is stated as: the
set of the vertices within distance ℓ of X separates S from T ([separator] of GraphTheory). *)

From GraphTheory Require Import digraph sgraph connectivity.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

Section Paths.
Variable G : diGraph.
Implicit Types (p : seq G) (X Y : {set G}).

(** [p] is a path (nonempty, without repetition). *)
Definition seq_simple_path p : bool := if p is x :: q then path (--) x q && uniq p else false.

(** [p] is a path from a vertex of [X] to a vertex of [Y]. *)
Definition seq_path_between X Y p : bool :=
  if p is x :: q then [&& x \in X, last x q \in Y & seq_simple_path p] else false.

End Paths.

(** The vertices of [G] at distance at most [k] from [x]. *)
Definition ball (G : sgraph) (k : nat) (x : G) : {set G} := iter k (@closed_neigh_set G) [set x].

(** The vertices at distance at most [r] from [S]. *)
Definition set_ball (G : sgraph) (r : nat) (S : {set G}) : {set G} :=
  \bigcup_(x in S) ball r x.

(** Distinct sequences of the list [paths] are at distance at least [d] ([0 < d] is meant). *)
Definition pairwise_distant_seqs (G : sgraph) (d : nat) (paths : seq (seq G)) : Prop :=
  forall p q : seq G, p \in paths -> q \in paths -> p != q ->
    [disjoint set_ball d.-1 [set:: p] & [set:: q]].

(** There are [k] paths from [X] to [Y] pairwise at distance at least [d]. *)
Definition has_distant_paths (G : sgraph) (d k : nat) (X Y : {set G}) : Prop :=
  exists paths : seq (seq G),
    size paths = k /\
    uniq paths /\
    (forall p : seq G, p \in paths -> seq_path_between X Y p) /\
    pairwise_distant_seqs d paths.

(** ** Statement *)

Definition AX_coarse_menger_distance_2_paths : Prop :=
  forall k : nat,
    1 <= k ->
    exists ell : nat,
      0 < ell /\
      forall (G : sgraph) (S T : {set G}),
        has_distant_paths 2 k S T \/
        exists X : {set G}, #|X| <= k - 1 /\ separator G S T (set_ball ell X).
