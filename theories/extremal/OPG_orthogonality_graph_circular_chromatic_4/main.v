(** * Circular colouring of the orthogonality graph

DeVos, Ghebleh, Goddyn, Mohar, Naserasr; Open Problem Garden,
circular_colouring_the_orthogonality_graph.

The orthogonality graph O has the lines through the origin of R³ as vertices, two lines being
adjacent if they are perpendicular.  A (p,q)-colouring of a graph gives to each vertex a colour in
{0, ..., p-1} such that q <= |i - j| <= p - q for the colours i and j of any two adjacent vertices.
The circular chromatic number χ_c is the infimum of the p/q such that there is a (p,q)-colouring.

Problem: is χ_c(O) = 4?  The proposition states the positive answer.

Encoding.  The vertices are the vectors, and two vectors are adjacent if they are not zero and their
scalar product is 0.  This is equivalent: the zero vector is an isolated vertex, and nonzero vectors
of the same line have the same neighbours, so that this graph and O have (p,q)-colourings for the
same p and q.  The infimum is required to be attained, which holds for the value 4: O has a proper
4-colouring, that is, a (4,1)-colouring.  The field R is an arbitrary real closed field (for
instance the real numbers), which is equivalent: the existence of a (p,q)-colouring depends only on
the finite subgraphs, which are the same for all real closed fields. *)

From mathcomp Require Import boot order algebra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.Theory GRing.Theory Num.Theory.

(** ** Definitions copied from GraphLib/chromatic.v *)

(** [c] is a circular [(p,q)]-colouring: its values are less than [p] and, for adjacent
    vertices, they differ by at least [q] and at most [p - q]. *)
Definition circular_coloring (V : Type) (adj : V -> V -> bool) (p q : nat) (c : V -> nat) : Prop :=
  (forall v, (c v < p)%N) /\
  (forall u v, adj u v ->
     (q <= absz (Posz (c u) - Posz (c v))%R)%N /\
     (absz (Posz (c u) - Posz (c v))%R <= p - q)%N).

(** The circular chromatic number is [r]: the least [p / q] such that there is a circular
    [(p,q)]-colouring (there is none if no two vertices are adjacent). *)
Definition circular_chromatic_number (V : Type) (adj : V -> V -> bool) (r : rat) : Prop :=
  (exists p q : nat, (0 < q)%N /\ (exists c, circular_coloring adj p q c) /\ r = (p%:Q / q%:Q)%R) /\
  (forall p q : nat, (0 < q)%N -> (exists c, circular_coloring adj p q c) -> (r <= p%:Q / q%:Q)%R).

(** ** Definitions specific to the conjecture *)

(** The vectors [u] and [v] are not zero and they are perpendicular. *)
Definition perpendicular (R : rcfType) (u v : 'rV[R]_3) : bool :=
  [&& u != 0, v != 0 & (u *m v^T) 0 0 == 0]%R.

(** ** Statement *)

Definition OPG_orthogonality_graph_circular_chromatic_4 : Prop :=
  forall R : rcfType, circular_chromatic_number (@perpendicular R) (4%:Q)%R.
