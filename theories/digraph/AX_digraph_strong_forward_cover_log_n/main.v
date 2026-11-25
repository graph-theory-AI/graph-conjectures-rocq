(** * Logarithmic forward covers of strong digraphs

Bessy, Thomassé, Viennot, "Temporalizing digraphs via linear-size balanced bi-trees",
STACS 2024, arXiv:2304.03567, Conjecture 1 (2304.03567__04).

A digraph is strong if every vertex has a directed path to every other.  Given a total order <
on the vertices of a digraph D, an arc xy is forward if x < y, and a couple (x,y) is forward if
there is a directed path from x to y using only forward arcs.  A forward cover of D is a set of
vertex orders such that, for every pair {x,y} of vertices, (x,y) or (y,x) is a forward couple
in at least one of these orders.

Conjecture 1: every strong digraph on n vertices has a forward cover of size O(log n).

Encoding.  Digraphs are those of GraphTheory ([diGraph]): a finite type of vertices with a
boolean relation [--].  Digons are allowed, as in the paper, and loops too, but a loop is
never forward.  A vertex order is an injective function to the natural numbers.  A forward
cover is a sequence of such functions, possibly with repetitions, which does not change the
minimum size.  O(log n) is read as: at most c ⌊log_2 n⌋ for all n >= n0, where c and n0 are
constants. *)

From GraphTheory Require Import digraph.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/digraph.v *)

(** [D] is strongly connected. *)
Definition strongly_connected (D : diGraph) : bool :=
  [forall x : D, forall y : D, connect (--) x y].

(** ** Definitions specific to the conjecture *)

(** The forward arcs for the ranking [r] of the vertices. *)
Definition forward_arc (D : diGraph) (r : D -> nat) : rel D :=
  fun u v => (u -- v) && (r u < r v).

(** [(x, y)] or [(y, x)] is a forward couple for [r]. *)
Definition forward_pair (D : diGraph) (r : D -> nat) (x y : D) : bool :=
  connect (forward_arc r) x y || connect (forward_arc r) y x.

(** [rs] is a forward cover of [D]: its members are injective (hence vertex orders), and every
    pair of distinct vertices is forward for some member. *)
Definition forward_cover (D : diGraph) (rs : seq {ffun D -> nat}) : Prop :=
  all (fun r : {ffun D -> nat} => injectiveb r) rs /\
  forall x y : D, x != y -> has (fun r : {ffun D -> nat} => forward_pair r x y) rs.

(** ** Statement *)

(** Strong digraphs on n vertices have forward covers of size O(log n). *)
Definition AX_digraph_strong_forward_cover_log_n : Prop :=
  exists c n0 : nat, forall D : diGraph, strongly_connected D -> n0 <= #|D| ->
    exists rs : seq {ffun D -> nat}, forward_cover rs /\ size rs <= c * trunc_log 2 #|D|.
