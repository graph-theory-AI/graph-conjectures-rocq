(** * Sidorenko's conjecture

Sidorenko; Open Problem Garden, sidorenkos_conjecture.

Conjecture: for every bipartite graph H and every graph G, the number of homomorphisms from H to G
is at least (2|E(G)| / |V(G)|^2)^|E(H)| |V(G)|^|V(H)|.

Encoding.  Graphs are finite and simple, and G is nonempty, so that the quotient is defined.  The
inequality is multiplied by |V(G)|^(2|E(H)|), and 2|E(G)| is the number of ordered pairs of adjacent
vertices ([num_edges]). *)

From GraphTheory Require Import digraph sgraph connectivity.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

(** [G] is bipartite: it has a bipartition (a set [A] such that each edge has exactly one end in
    [A]). *)
Definition bipartite (G : diGraph) : Prop := exists A : {set G}, bipartition A.

(** ** Definitions copied from GraphLib/homomorphism.v *)

(** The number of homomorphisms from [H] to [G] (of endomorphisms of [G] if [H] is [G]). *)
Definition hom_count (H G : diGraph) : nat :=
  #|[set f : {ffun H -> G} | [forall x : H, [forall y : H, (x -- y) ==> (f x -- f y)]]]|.

(** ** Statement *)

Definition OPG_sidorenko_bipartite_homomorphism_density : Prop :=
  forall H G : sgraph, bipartite H -> 0 < #|G| ->
    num_edges G ^ #|E(H)| * #|G| ^ #|H| <= hom_count H G * #|G| ^ (2 * #|E(H)|).
