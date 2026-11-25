(** * Number of 3-colourings of triangle-free planar graphs

Dvořák, Postle, "Triangle-free planar graphs with at most 64^(n^0.731) 3-colorings",
arXiv:2108.12669, Conjecture 1 (2108.12669__00).

Conjecture 1: there exists a constant c > 1 such that every n-vertex triangle-free planar graph has
at least c^(n^α) distinct proper 3-colourings, where α = log_{9/2} 3 ≈ 0.7304.

Encoding.  Graphs are finite, simple and nonempty.  Planarity is the absence of minors K_5 and
K_3,3.  Colourings are maps to {0,1,2}, not considered up to a permutation of the colours.

To avoid real numbers, the bound on the number N of colourings is stated as 2^m <= N^k, for a
constant k > 0, for all natural numbers a, b, m such that a/b < α (that is, 9^a < 3^b 2^a) and
m <= n^(a/b) (that is, m^b <= n^a).  This is equivalent.  Given c, take k such that c^k >= 2.  Given
k, take c = 2^(1/(2k)): if n^α < 2 then a = 0, m = 1 gives N >= 2, and otherwise the largest integer
m < n^α satisfies m <= n^(a/b) for some a/b < α, and m >= n^α / 2. *)

From GraphTheory Require Import digraph sgraph coloring minor.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

(** [G] has no triangle. *)
Definition triangle_free (G : sgraph) : Prop :=
  forall x y z : G, x -- y -> y -- z -> z -- x -> False.

(** ** Definitions copied from GraphLib/chromatic.v *)

(** [col] is a proper colouring of [G]. *)
Definition proper_coloring (G : sgraph) (C : finType) (col : G -> C) : bool :=
  coloring (preim_partition col [set: G]) [set: G].

(** ** Definitions copied from GraphLib/topological.v *)

(** [G] is planar: it has no minor [K_5] or [K_3,3]. *)
Definition planar (G : sgraph) : Prop :=
  ~ minor G 'K_5 /\ ~ minor G (KB 3 3).

(** ** Statement *)

Definition AX_triangle_free_planar_3_coloring_count : Prop :=
  exists k : nat, 0 < k /\
    forall G : sgraph, 0 < #|G| -> planar G -> triangle_free G ->
      forall a b m : nat, 9 ^ a < 3 ^ b * 2 ^ a -> m ^ b <= #|G| ^ a ->
        2 ^ m <= #|[set f : {ffun G -> 'I_3} | proper_coloring f]| ^ k.
