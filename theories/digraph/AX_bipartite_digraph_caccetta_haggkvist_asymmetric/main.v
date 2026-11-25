(** * Short directed cycles in bipartite digraphs, asymmetric version

Seymour, Spirkl, "Short directed cycles in bipartite digraphs", 2018, arXiv:1809.08324, Conjecture
1.5 (1809.08324__01).

A digraph is bipartite, with bipartition (A,B), if (A,B) is a partition of its vertices and each arc
has one end in A and the other one in B.  A digraph has girth at most g if it has a directed cycle
of length at most g.

Conjecture: for every integer k >= 1 and all reals α, β > 0 with kα + β > 1, if a non-null digraph
is bipartite with bipartition (A,B), every vertex of A has out-degree at least β|B|, and every
vertex of B has out-degree at least α|A|, then this digraph has girth at most 2k.

Encoding.  Digraphs are those of GraphTheory ([diGraph]: a finite type of vertices with a boolean
relation [--]).  Digons are allowed, as in the source; they are directed cycles of length two.  The
part B is the complement of A.  A and B are nonempty: if one of them is empty, then there is no
arc and the condition on the out-degrees is trivial.  The numbers α and β are in an arbitrary
ordered field (the rational or real numbers for instance), which is equivalent: α can be replaced by
the minimum out-degree in B divided by |A|, and β by the minimum out-degree in A divided by |B|. *)

From GraphTheory Require Import digraph connectivity.
From mathcomp Require Import boot order algebra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/digraph.v *)

(** Out-degree. *)
Definition outdeg (D : diGraph) (v : D) : nat := #|N(v)|.

(** The vertices [c] form a directed cycle, of length [size c] (a loop or a digon is one). *)
Definition dicycle (D : diGraph) (c : seq D) : bool := ~~ nilp c && ucycleb (--) c.

(** ** Statement *)

Definition AX_bipartite_digraph_caccetta_haggkvist_asymmetric : Prop :=
  forall (R : realFieldType) (k : nat) (alpha beta : R),
    1 <= k -> (0 < alpha)%R -> (0 < beta)%R -> (1 < k%:R * alpha + beta)%R ->
    forall (D : diGraph) (A : {set D}),
      A != set0 -> ~: A != set0 -> bipartition A ->
      (forall v : D, v \in A -> (beta * #|~: A|%:R <= (outdeg v)%:R)%R) ->
      (forall v : D, v \notin A -> (alpha * #|A|%:R <= (outdeg v)%:R)%R) ->
      exists c : seq D, dicycle c /\ size c <= 2 * k.
