(** * Monochromatic vertex colourings inherited from perfect matchings

Krenn, Gu, Soltész, "Questions on the structure of perfect matchings inspired by quantum physics",
arXiv:1902.06023; Open Problem Garden,
monochromatic_vertex_colorings_inherited_from_perfect_matchings.

A bi-coloured weighted graph on the vertices v_1, ..., v_n with d colours is a graph, possibly with
parallel edges, with a complex weight on each edge e = v_i v_j, i < j, and an ordered pair
(c_1(e), c_2(e)) of colours, not necessarily distinct: e has colour c_1(e) at v_i and c_2(e) at v_j.
The vertex colouring inherited from a perfect matching M gives to each vertex v the colour at v of
the edge of M incident to v.  The weight of a vertex colouring c is the sum, over the perfect
matchings whose inherited vertex colouring is c, of the products of the weights of their edges.

Problem: for which values of n and d is there a bi-coloured weighted graph on n vertices with d
colours such that the d monochromatic vertex colourings have weight 1 and the other ones have
weight 0?

The proposition states the answer conjectured by Krenn and Gu: for n, d >= 1, if and only if n = 2,
or n is even and d <= 2, or n = 4 and d <= 3.  (In these cases, the edges with nonzero weight can
be those of d parallel edges, of a cycle and of K_4 respectively.)

Encoding.  The weight w i j a b, for i < j, is the sum of the weights of the edges between i and j
with colour a at i and colour b at j (0 if there is none): parallel edges with the same colours can
be merged without changing the weights of the vertex colourings.  The other values of w are
irrelevant.  A perfect matching is an involution without fixed point.  The weights are in an
arbitrary algebraically closed field of characteristic 0 ([numClosedFieldType]), for instance the
complex numbers; this is equivalent, as the conditions are polynomial equations with integer
coefficients (Nullstellensatz).  The restriction to n, d >= 1 is implicit in the problem. *)

From mathcomp Require Import boot order algebra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.Theory GRing.Theory Num.Theory.

(** ** Definitions specific to the conjecture *)

Section Weights.
Variables (C : numClosedFieldType) (n d : nat) (w : 'I_n -> 'I_n -> 'I_d -> 'I_d -> C).
Local Open Scope ring_scope.

(** [m] is a perfect matching: [m i] is the vertex matched with [i]. *)
Definition matching_involution (m : {ffun 'I_n -> 'I_n}) : bool :=
  [forall i, (m (m i) == i) && (m i != i)].

(** The weight of the vertex colouring [c]. *)
Definition vertex_coloring_weight (c : 'I_n -> 'I_d) : C :=
  \sum_(m : {ffun 'I_n -> 'I_n} | matching_involution m)
    \prod_(i : 'I_n | (i < m i)%N) w i (m i) (c i) (c (m i)).

(** The monochromatic vertex colourings have weight 1 and the other ones have weight 0. *)
Definition only_monochromatic : Prop :=
  forall c : 'I_n -> 'I_d, vertex_coloring_weight c = [forall i, forall j, c i == c j]%:R.

End Weights.

(** ** Statement *)

Definition OPG_perfect_matching_inherited_colorings_cancellation : Prop :=
  forall (C : numClosedFieldType) (n d : nat), 0 < n -> 0 < d ->
    (exists w : 'I_n -> 'I_n -> 'I_d -> 'I_d -> C, only_monochromatic w) <->
    [|| n == 2, ~~ odd n && (d <= 2) | (n == 4) && (d <= 3)].
