(** * The Gyárfás-Sumner conjecture, as an equivalence

Aboulker, Bang-Jensen, Bousquet, Charbit, Havet, Maffray, Zamora, "χ-bounded families of oriented
graphs", 2016, arXiv:1605.07411, Conjecture 2 (1605.07411__00).

A class of graphs is χ-bounded if there is a function f such that χ(G) <= f(ω(G)) for every graph G
of the class, where ω(G) is the clique number of G.  For a graph H, Forb(H) is the class of graphs
with no induced subgraph isomorphic to H.

Conjecture: Forb(H) is χ-bounded if and only if H is a forest.

Encoding.  Graphs are finite, simple and undirected, as in this conjecture of the source. *)

From GraphTheory Require Import digraph sgraph coloring.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

(** [G] has an induced subgraph isomorphic to [H]. *)
Definition has_induced_copy (G H : sgraph) : Prop := inhabited (H ⇀ G).

(** [G] has no induced subgraph isomorphic to [H]. *)
Definition induced_free (G H : sgraph) : Prop := ~ has_induced_copy G H.

(** ** Definitions copied from GraphLib/chromatic.v *)

(** The class [F] is chi-bounded: on its graphs, the chromatic number is bounded by a function
    of the clique number. *)
Definition chi_bounded (F : sgraph -> Prop) : Prop :=
  exists f : nat -> nat,
    forall G : sgraph, F G -> χ([set: G]) <= f (ω([set: G])).

(** ** Statement *)

Definition AX_gyarfas_sumner_oriented_iff_forest : Prop :=
  forall H : sgraph,
    chi_bounded (fun G : sgraph => induced_free G H) <-> is_forest [set: H].
