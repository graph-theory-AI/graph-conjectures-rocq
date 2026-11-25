(** * Distant paths in graphs of bounded degree: an induced version of Menger's theorem

Hendrey, Norin, Steiner, Turcotte, "On an induced version of Menger's theorem", arXiv:2309.07905,
Conjecture 1.4 (2309.07905__00).

Let X and Y be sets of vertices of a graph G.  An X-Y path has one end in X and the other one in Y
(a single vertex of X ∩ Y is an X-Y path).  A set of vertices separates X and Y if it meets every
X-Y path.  The distance between two paths is the minimum distance in G between their vertices.

Conjecture: for all natural numbers d and Δ, there is a constant C > 0 such that, for every natural
number k, every graph G of maximum degree at most Δ, and all sets of vertices X and Y of G, either
there are k X-Y paths pairwise at distance at least d, or X and Y are separated by a set of less
than Ck vertices.

Encoding.  Graphs are finite and simple.  The constant C is an integer, without loss of generality.
A path is a sequence of vertices.  Two paths are at distance at least d if no vertex of one is at
distance at most d-1 from a vertex of the other.  The case d = 0 is read as the case d = 1 (disjoint
paths, Menger's theorem).  [separator G X Y Z] (GraphTheory) says that Z meets every X-Y path. *)

From GraphTheory Require Import digraph sgraph connectivity.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

(** The maximum degree of [G] (0 if [G] is empty). *)
Definition Delta (G : sgraph) : nat := \max_(x : G) #|N(x)|.

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

Definition AX_induced_menger_bounded_degree_linear_separator : Prop :=
  forall d Dmax : nat, exists C : nat,
    0 < C /\
    forall (k : nat) (G : sgraph) (X Y : {set G}),
      Delta G <= Dmax ->
      has_distant_paths d k X Y \/
      exists Z : {set G}, #|Z| < C * k /\ separator G X Y Z.
