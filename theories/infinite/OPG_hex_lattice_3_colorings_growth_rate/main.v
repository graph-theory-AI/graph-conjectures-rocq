(** * Counting 3-colourings of the hexagonal lattice

Thomassen; Open Problem Garden, counting_3_colorings_of_the_hex_lattice.

For n >= 1, let T_n be the triangulation of the torus obtained from a regular hexagonal piece of
side-length n of the triangular tiling of the plane by identifying opposite sides.  Let H_n be the
dual of T_n: a hexagonal tiling of the torus.  Let χ(G,k) be the number of proper k-colourings of
a graph G.

Problem: find the limit of χ(H_n,3)^(1/|V(H_n)|) as n tends to infinity.

The proposition states that this limit exists.

Encoding.  The problem suggests no value for the limit, so the proposition is only a proxy, weaker
than a determination of the limit.

The hexagonal tiling of the plane is obtained from the triangular lattice, whose points are the
pairs of integers where (x,y) is adjacent to (x,y) ± (1,0), (x,y) ± (0,1) and (x,y) ± (1,-1), by
removing the points such that x = y modulo 3, which are the centers of the hexagons.  These
centers form a triangular lattice, and identifying the opposite sides of the hexagon of
side-length n of this lattice amounts to computing modulo 3n.  Hence H_n has the 6n² pairs (x,y)
of integers modulo 3n with x <> y modulo 3 as vertices.  If x - y = 1 modulo 3, then the neighbours
of (x,y) are (x,y) + (1,0), (x,y) + (0,-1) and (x,y) + (-1,1).

The convergence of a sequence of nonnegative numbers is expressed without roots and real numbers:
for every rational ε > 0, there is a rational a >= 0 such that the terms of the sequence are in
[a, a+ε] from some index on. *)

From GraphTheory Require Import preliminaries digraph sgraph coloring.
From mathcomp Require Import boot order algebra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.Theory GRing.Theory Num.Theory.

(** ** Definitions copied from GraphLib/misc.v *)

Lemma sgraph_of_rel_sym (V : finType) (r : rel V) :
  symmetric (fun x y => (x != y) && sc r x y).
Proof. by move=> x y /=; rewrite eq_sym orbC. Qed.

Lemma sgraph_of_rel_irrefl (V : finType) (r : rel V) :
  irreflexive (fun x y => (x != y) && sc r x y).
Proof. by move=> x; rewrite eqxx. Qed.

(** The graph on [V] whose edges are given by [r], up to symmetry and loops. *)
Definition sgraph_of_rel (V : finType) (r : rel V) : sgraph :=
  SGraph (@sgraph_of_rel_sym V r) (@sgraph_of_rel_irrefl V r).

(** ** Definitions copied from GraphLib/chromatic.v *)

(** [col] is a proper colouring of [G]. *)
Definition proper_coloring (G : sgraph) (C : finType) (col : G -> C) : bool :=
  coloring (preim_partition col [set: G]) [set: G].

(** The number of proper colourings of [G] with [k] colours. *)
Definition num_colorings (G : sgraph) (k : nat) : nat :=
  #|[set c : {ffun G -> 'I_k} | proper_coloring c]|.

(** ** Definitions specific to the conjecture *)

(** The hexagonal tiling H_n of the torus ([1 <= n] is meant). *)
Definition hex_torus (n : nat) : sgraph :=
  @sgraph_of_rel {p : 'Z_(3 * n) * 'Z_(3 * n) | p.1 != p.2 %[mod 3]}
    (fun u v => (val v - val u)%R \in [:: (1, 0); (0, -1); (-1, 1)]%R).

(** The sequence of the roots of order [d n] of [c n] converges to a limit. *)
Definition roots_converge (c d : nat -> nat) : Prop :=
  forall eps : rat, (0 < eps)%R ->
    exists (a : rat) (N : nat), (0 <= a)%R /\
      forall n : nat, N <= n -> (a ^+ d n <= (c n)%:R <= (a + eps) ^+ d n)%R.

(** ** Statement *)

Definition proxy_OPG_hex_lattice_3_colorings_growth_rate : Prop :=
  roots_converge (fun n => num_colorings (hex_torus n) 3) (fun n => #|hex_torus n|).
