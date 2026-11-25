(** * List chromatic number at most a fraction of Δ for graphs without large cliques

Bonamy, Kelly, Nelson, Postle, "Bounding χ by a fraction of Δ for graphs without large cliques",
arXiv:1803.01051, Question 1.5 (1803.01051__00).

The list chromatic number χ_l(G) is the least k such that G has a proper colouring from all lists of
at least k colours on its vertices.

Question 1.5: does there exist a function f from R to R such that for every c > 1 and every graph G
of maximum degree at most Δ with no clique of size greater than Δ^(1/f(c)), we have
χ_l(G) <= Δ/c?

The proposition states the positive answer, where Δ is the maximum degree of G.

Encoding.  Graphs are finite and simple.  The real number c is replaced by a rational number a/b
with a > b > 0, and f(c), which is meant to be positive, by a positive integer f(a,b): this is
equivalent, as increasing f(c) strengthens the hypothesis.  This hypothesis is written
ω(G)^f(a,b) <= Δ(G), and the conclusion a m <= b Δ(G), where m is the list chromatic number of G
("χ_l(G) = m" is a relation between G and m).  The hypothesis implies Δ(G) >= 2^f(a,b) when G has a
vertex.  If Δ were any upper bound of the maximum degree, the one-vertex graph with Δ = 1 would be a
counterexample; for upper bounds Δ larger than some constant depending on c, the statement would be
equivalent to this one (add a disjoint star with Δ edges to G). *)

From GraphTheory Require Import digraph sgraph coloring.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

(** The maximum degree of [G] (0 if [G] is empty). *)
Definition Delta (G : sgraph) : nat := \max_(x : G) #|N(x)|.

(** ** Definitions copied from GraphLib/chromatic.v *)

(** [f] is a proper colouring from the lists [L]. *)
Definition proper_list_coloring
    (G : sgraph) (C : finType) (L : G -> {set C}) (f : G -> C) : Prop :=
  (forall v : G, f v \in L v) /\
  (forall x y : G, x -- y -> f x != f y).

(** [G] has a proper colouring from the lists [L]. *)
Definition list_colorable (G : sgraph) (C : finType) (L : G -> {set C}) : Prop :=
  exists f : G -> C, proper_list_coloring L f.

(** [G] is [k]-choosable. *)
Definition choosable (G : sgraph) (k : nat) : Prop :=
  forall (C : finType) (L : G -> {set C}),
    (forall v : G, k <= #|L v|) -> list_colorable L.

(** The choice number (list chromatic number) of [G] is [m]. *)
Definition choice_number (G : sgraph) (m : nat) : Prop :=
  choosable G m /\ (forall k, choosable G k -> m <= k).

(** ** Statement *)

Definition AX_list_chromatic_fraction_delta_small_clique : Prop :=
  exists f : nat -> nat -> nat,
    forall a b : nat, 0 < b -> b < a ->
      0 < f a b /\
      forall (G : sgraph) (m : nat),
        choice_number G m ->
        ω([set: G]) ^ f a b <= Delta G ->
        a * m <= b * Delta G.
