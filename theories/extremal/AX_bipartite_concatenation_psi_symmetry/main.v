(** * Symmetry of ψ in the concatenation of bipartite graphs

Chudnovsky, Hompe, Scott, Seymour, Spirkl, "Concatenating bipartite graphs", arXiv:1902.10878,
open question on the symmetry of ψ (biconstrained case).

A tripartition of a graph G is a partition (A,B,C) of V(G) into three nonempty stable sets.  For
x, y in (0,1], G is (x,y)-biconstrained via (A,B,C) if there are no edges between A and C and
- every vertex of A has at least x|B| neighbours in B,
- every vertex of B has at least y|C| neighbours in C,
- every vertex of B has at least x|A| neighbours in A,
- every vertex of C has at least y|B| neighbours in B.

For a vertex v, N²_A(v) is the set of vertices of A at distance exactly two from v.  Let ψ(x,y) be
the maximum z such that, for every graph that is (x,y)-biconstrained via some (A,B,C), there is a
vertex v in C with |N²_A(v)| >= z|A| (this maximum exists).

Question: does ψ(x,y) = ψ(y,x) hold for all x, y in (0,1]?  The proposition states the positive
answer.

Encoding.  Graphs are finite and simple.  The equality ψ(x,y) = ψ(y,x) is expressed by the
equivalence of ψ(x,y) >= z and ψ(y,x) >= z for all rational z.  The numbers x and y are rational,
which is equivalent: a finite graph is (x,y)-biconstrained for real numbers x and y if and only if
it is for some rational numbers x' >= x and y' >= y in (0,1], so that ψ(x,y) is the infimum of these
ψ(x',y'). *)

From GraphTheory Require Import preliminaries digraph sgraph dom.
From mathcomp Require Import boot order algebra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.Theory GRing.Theory Num.Theory.

(** ** Definitions copied from GraphLib/misc.v *)

(** The common neighbours of [u] and [v]. *)
Definition common_neigh (G : sgraph) (u v : G) : {set G} := N(u) :&: N(v).

(** ** Definitions specific to the conjecture *)

Local Open Scope ring_scope.

(** The vertices at distance exactly two from [v]. *)
Definition second_neigh (G : sgraph) (v : G) : {set G} :=
  [set u | [&& u != v, ~~ (u -- v) & common_neigh u v != set0]].

(** [(A, B, C)] is a tripartition of [G]. *)
Definition tripartition (G : sgraph) (A B C : {set G}) : bool :=
  [&& A :|: B :|: C == [set: G],
      [disjoint A & B], [disjoint B & C], [disjoint A & C],
      [&& A != set0, B != set0 & C != set0] &
      [&& stable A, stable B & stable C]].

(** [G] is [(x,y)]-biconstrained via [(A, B, C)]. *)
Definition biconstrained (G : sgraph) (x y : rat) (A B C : {set G}) : bool :=
  [&& tripartition A B C,
      [forall a in A, forall c in C, ~~ (a -- c)],
      [forall a in A, x * #|B|%:R <= #|N(a) :&: B|%:R],
      [forall b in B, y * #|C|%:R <= #|N(b) :&: C|%:R],
      [forall b in B, x * #|A|%:R <= #|N(b) :&: A|%:R] &
      [forall c in C, y * #|B|%:R <= #|N(c) :&: B|%:R]].

(** ψ(x,y) >= z. *)
Definition psi_ge (x y z : rat) : Prop :=
  forall (G : sgraph) (A B C : {set G}),
    biconstrained x y A B C ->
    exists2 c : G, c \in C & z * #|A|%:R <= #|A :&: second_neigh c|%:R.

(** ** Statement *)

Definition AX_bipartite_concatenation_psi_symmetry : Prop :=
  forall x y z : rat, 0 < x <= 1 -> 0 < y <= 1 -> (psi_ge x y z <-> psi_ge y x z).
