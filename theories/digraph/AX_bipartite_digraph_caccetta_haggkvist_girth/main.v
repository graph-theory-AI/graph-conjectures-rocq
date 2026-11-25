(** * A bipartite analogue of the Caccetta-Häggkvist conjecture

Seymour, Spirkl, "Short directed cycles in bipartite digraphs", 2018, arXiv:1809.08324, Conjecture
1.2 (1809.08324__00).

A digraph is bipartite, with parts A and B, if (A,B) is a partition of its vertices and each arc has
one end in A and the other one in B.  A digraph has girth at most g if it has a directed cycle of
length at most g.

Conjecture: for every integer k >= 1, if a bipartite digraph has n > 0 vertices in each part, and if
every vertex has out-degree more than n/(k+1), then this digraph has girth at most 2k.

Encoding.  Digraphs are those of GraphTheory ([diGraph]: a finite type of vertices with a boolean
relation [--]).  Digons are allowed, as in the source; they are directed cycles of length two.  The
part B is the complement of A. *)

From GraphTheory Require Import digraph connectivity.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/digraph.v *)

(** Out-degree. *)
Definition outdeg (D : diGraph) (v : D) : nat := #|N(v)|.

(** The vertices [c] form a directed cycle, of length [size c] (a loop or a digon is one). *)
Definition dicycle (D : diGraph) (c : seq D) : bool := ~~ nilp c && ucycleb (--) c.

(** ** Statement *)

Definition AX_bipartite_digraph_caccetta_haggkvist_girth : Prop :=
  forall (k n : nat) (D : diGraph) (A : {set D}),
    1 <= k -> 0 < n ->
    bipartition A -> #|A| = n -> #|~: A| = n ->
    (forall v : D, n < k.+1 * outdeg v) ->
    exists c : seq D, dicycle c /\ size c <= 2 * k.
