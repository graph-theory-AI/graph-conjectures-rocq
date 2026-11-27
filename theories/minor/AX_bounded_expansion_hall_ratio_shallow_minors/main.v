(** * Bounded expansion and Hall ratio of shallow minors

Dvořák, Ossona de Mendez, Wu, "1-subdivisions, fractional chromatic number and Hall ratio",
arXiv:1812.07327, Problem 8 (1812.07327__02).

The Hall ratio ρ(G) is the maximum of |V(K)| / α(K) over the nonempty subgraphs K of G.  A shallow
minor of G at depth r is a graph obtained from G by deleting vertices and edges and contracting
disjoint subgraphs of radius at most r; C ▽ r is the class of the shallow minors at depth r of the
graphs of C.  The class C has bounded expansion if there is a function f_1 such that, for every r,
every graph of C ▽ r has average degree at most f_1(r).

Problem 8: is it true that a class C has bounded expansion if and only if there exists a function
f_6 : ℕ -> ℕ such that ρ(G) <= f_6(r) for every r in ℕ and every G in C ▽ r?  The positive answer is
stated.

Encoding.  Classes of graphs are arbitrary predicates.  The bound f_1 has values in nat, which is
not a restriction.  The bounds on quotients are multiplied by the denominators, which makes them
trivial for empty graphs.  [subgraph K H] means that K is isomorphic to a subgraph of H, not
necessarily induced. *)

From GraphTheory Require Import digraph sgraph coloring minor.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

(** The vertices of [G] at distance at most [k] from [x]. *)
Definition ball (G : sgraph) (k : nat) (x : G) : {set G} := iter k (@closed_neigh_set G) [set x].

(** ** Definitions copied from GraphLib/minor.v *)

(** [H] is a minor of [G] at depth [r]: the branch sets have radius at most [r]. *)
Definition shallow_minor (G H : sgraph) (r : nat) : Prop :=
  exists2 B : H -> {set G}, minor_rmap B &
    forall x : H, exists c : induced (B x), ball r c = [set: induced (B x)].

(** The class [C] has bounded expansion: the average degree of its minors at depth [r] is bounded
    by a function of [r]. *)
Definition bounded_expansion (C : sgraph -> Prop) : Prop :=
  exists f : nat -> nat, forall (r : nat) (G H : sgraph),
    C G -> shallow_minor G H r -> 2 * #|E(H)| <= f r * #|H|.

(** ** Definitions copied from GraphLib/fractional.v *)

(** The Hall ratio of [G] is at most [p / q]: so is the ratio of the number of vertices to the
    independence number for all its subgraphs. *)
Definition hall_ratio_le (G : sgraph) (p q : nat) : Prop :=
  forall H : sgraph, subgraph H G -> q * #|H| <= p * α([set: H]).

(** ** Definitions specific to the conjecture *)

(** The Hall ratio of the shallow minors at depth [r] of the class [C] is bounded by a function
    of [r]. *)
Definition bounded_hall_ratio_of_shallow_minors (C : sgraph -> Prop) : Prop :=
  exists f6 : nat -> nat, forall (r : nat) (G H : sgraph),
    C G -> shallow_minor G H r -> hall_ratio_le H (f6 r) 1.

(** ** Statement *)

Definition AX_bounded_expansion_hall_ratio_shallow_minors : Prop :=
  forall C : sgraph -> Prop,
    bounded_expansion C <-> bounded_hall_ratio_of_shallow_minors C.
