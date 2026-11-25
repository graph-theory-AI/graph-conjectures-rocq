(** * Chromatic number of common graphs

Hatami, Hladký, Kráľ, Norine, Razborov, "Non-three-colorable common graphs exist", Combin. Probab.
Comput. 21 (2012); Open Problem Garden, chromatic_number_of_common_graphs.

A graph H is common if the number of copies of H in a graph G plus the number of copies of H in the
complement of G is asymptotically minimised when G is a random graph.

Question: do common graphs have bounded chromatic number?  What is stated is the positive answer:
there is a k such that every common graph is k-colourable.

Encoding.  Copies are counted as homomorphisms, as usual in the definition of common graphs; those
that are not injective are negligible.  For a random graph G = G(n,1/2), the expected proportion of
homomorphisms among the n^|V(H)| maps from V(H) to V(G) tends to 2^(-|E(H)|), and the same holds for
the complement of G.  Hence H is common if, for every ε > 0 and every large enough n, the total
number of homomorphisms from H to G and to its complement is at least (2 - ε) 2^(-|E(H)|) n^|V(H)|
for every graph G with n vertices.  It suffices to take ε = 1/m for the integers m >= 1. *)

From GraphTheory Require Import digraph sgraph coloring.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

(** [P n] holds for every sufficiently large [n]. *)
Definition eventually (P : nat -> Prop) : Prop :=
  exists N : nat, forall n : nat, N <= n -> P n.

(** ** Definitions copied from GraphLib/homomorphism.v *)

(** The number of homomorphisms from [H] to [G] (of endomorphisms of [G] if [H] is [G]). *)
Definition hom_count (H G : diGraph) : nat :=
  #|[set f : {ffun H -> G} | [forall x : H, [forall y : H, (x -- y) ==> (f x -- f y)]]]|.

(** ** Definitions copied from GraphLib/extremal.v *)

(** [H] is common: the density of homomorphisms from [H] to a large graph plus the density to its
    complement is at least [2^(1 - m)] (up to [o(1)]), where [m] is the number of edges of [H]. *)
Definition common_graph (H : sgraph) : Prop :=
  forall m : nat, 0 < m -> eventually (fun n =>
    forall G : sgraph, #|G| = n ->
      2 * m * n ^ #|H| <= m * 2 ^ #|E(H)| * (hom_count H G + hom_count H (compl G)) + n ^ #|H|).

(** ** Statement *)

Definition OPG_common_graphs_bounded_chromatic_number : Prop :=
  exists k : nat, forall H : sgraph, common_graph H -> χ([set: H]) <= k.
