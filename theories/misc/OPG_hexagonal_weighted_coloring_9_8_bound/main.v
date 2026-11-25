(** * Weighted colouring of hexagonal graphs

McDiarmid, Reed, "Channel assignment and weighted coloring", Networks 36 (2000);
Open Problem Garden, weighted_colouring_of_hexagonal_graphs.

The vertices of the triangular lattice are the points a e1 + b e2 of the plane, where a and b
are integers, e1 = (1,0) and e2 = (1/2, √3/2).  Two of them are adjacent if their Euclidean
distance is 1.  A hexagonal graph is a (finite) induced subgraph of the triangular lattice.

Let p assign a nonnegative integer weight p(v) to each vertex v of a graph G.  The weighted
clique number ω(G,p) is the maximum weight of a clique.  A k-colouring of (G,p) assigns to each
vertex v a set of p(v) colours among k, in such a way that adjacent vertices receive disjoint
sets.  The weighted chromatic number χ(G,p) is the minimum k such that (G,p) has a
k-colouring.

Conjecture: there is a constant c such that χ(G,p) <= (9/8) ω(G,p) + c for every hexagonal
graph G and every weighting p.

Encoding.  The points of the lattice are represented by their coordinates (a,b), which are
taken nonnegative: this is not a restriction, as G is finite.  The inequality is multiplied
by 8. *)

From GraphTheory Require Import digraph sgraph.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

(** The adjacency of the triangular lattice, in coordinates. *)
Definition triangular_lattice_adj (a b : nat * nat) : bool :=
  let: (x1, y1) := a in let: (x2, y2) := b in
  [|| ((x2 == x1.+1) && (y2 == y1)),
      ((x1 == x2.+1) && (y1 == y2)),
      ((x1 == x2) && (y2 == y1.+1)),
      ((x1 == x2) && (y1 == y2.+1)),
      ((x2 == x1.+1) && (y1 == y2.+1)) |
      ((x1 == x2.+1) && (y2 == y1.+1))].

(** [G] is hexagonal: an induced subgraph of the triangular lattice. *)
Definition hexagonal (G : sgraph) : Prop :=
  exists phi : G -> nat * nat,
    injective phi /\
    (forall u v : G, u != v -> (u -- v) = triangular_lattice_adj (phi u) (phi v)).

(** ** Definitions copied from GraphLib/chromatic.v *)

(** The maximum weight of a clique, for the weights [p], is [w]. *)
Definition weighted_clique_number (G : sgraph) (p : G -> nat) (w : nat) : Prop :=
  (exists Q : {set G}, clique Q /\ \sum_(v in Q) p v = w) /\
  (forall Q : {set G}, clique Q -> \sum_(v in Q) p v <= w).

(** There is a weighted colouring with [k] colours: each vertex [v] receives a set of [p v]
    colours, and adjacent vertices receive disjoint sets. *)
Definition weighted_colorable (G : sgraph) (p : G -> nat) (k : nat) : Prop :=
  exists f : G -> {set 'I_k},
    (forall v : G, #|f v| = p v) /\
    (forall x y : G, x -- y -> [disjoint f x & f y]).

(** The weighted chromatic number is [k]. *)
Definition weighted_chromatic_number (G : sgraph) (p : G -> nat) (k : nat) : Prop :=
  weighted_colorable p k /\ (forall m : nat, weighted_colorable p m -> k <= m).

(** ** Statement *)

Definition OPG_hexagonal_weighted_coloring_9_8_bound : Prop :=
  exists c : nat,
    forall (G : sgraph) (p : G -> nat) (chi omega : nat),
      hexagonal G ->
      weighted_chromatic_number p chi ->
      weighted_clique_number p omega ->
      8 * chi <= 9 * omega + 8 * c.
