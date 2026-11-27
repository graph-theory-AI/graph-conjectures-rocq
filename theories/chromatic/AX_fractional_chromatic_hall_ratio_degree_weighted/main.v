(** * Fractional chromatic number, Hall ratio and degree weights

Dvořák, Ossona de Mendez, Wu, "1-subdivisions, fractional chromatic number and Hall ratio",
arXiv:1812.07327, Problem 5 (1812.07327__01).

The fractional chromatic number of G is the minimum of a/b over the colourings that give to each
vertex b of a colours, adjacent vertices receiving disjoint sets.  The Hall ratio ρ(G) is the
maximum of |V(H)| / α(H) over the subgraphs H of G.  For a graph H, let α_deg(H) be the maximum,
over the independent sets Y of H, of the sum of the degrees in H of the vertices of Y.

Problem 5: do there exist, for some constant c > 0, graphs G of arbitrarily large fractional
chromatic number such that ρ(G) <= c and α_deg(H) >= |E(H)| / c for every subgraph H of G?  The
positive answer is stated.

Encoding.  The constant c is a rational p/q, which is not a restriction, and the inequalities are
multiplied by q.  Subgraphs, not necessarily induced, are taken up to isomorphism. *)

From GraphTheory Require Import digraph sgraph dom coloring.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/chromatic.v *)

(** There is a weighted colouring with [k] colours: each vertex [v] receives a set of [p v]
    colours, and adjacent vertices receive disjoint sets. *)
Definition weighted_colorable (G : sgraph) (p : G -> nat) (k : nat) : Prop :=
  exists f : G -> {set 'I_k},
    (forall v : G, #|f v| = p v) /\
    (forall x y : G, x -- y -> [disjoint f x & f y]).

(** ** Definitions copied from GraphLib/fractional.v *)

(** The fractional chromatic number of [G] is at most [p / q] ([0 < q] is meant): [G] has a
    [b]-fold colouring with [a] colours (each vertex receives [b] colours, and adjacent vertices
    receive disjoint sets) such that [a / b <= p / q]. *)
Definition fractional_chromatic_le (G : sgraph) (p q : nat) : Prop :=
  exists a b : nat, [/\ 0 < b, weighted_colorable (fun _ : G => b) a & a * q <= p * b].

(** The Hall ratio of [G] is at most [p / q]: so is the ratio of the number of vertices to the
    independence number for all its subgraphs. *)
Definition hall_ratio_le (G : sgraph) (p q : nat) : Prop :=
  forall H : sgraph, subgraph H G -> q * #|H| <= p * α([set: H]).

(** ** Statement *)

Definition AX_fractional_chromatic_hall_ratio_degree_weighted : Prop :=
  exists p q : nat,
    [/\ 0 < p, 0 < q &
        forall F : nat, exists G : sgraph,
          [/\ ~ fractional_chromatic_le G F 1, hall_ratio_le G p q &
              forall H : sgraph, subgraph H G ->
                exists I : {set H}, stable I /\ q * #|E(H)| <= p * \sum_(v in I) #|N(v)|]].
