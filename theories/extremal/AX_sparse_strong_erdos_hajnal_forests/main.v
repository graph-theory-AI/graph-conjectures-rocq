(** * Graphs with the sparse strong Erdős-Hajnal property

Liebenau, Pilipczuk, Seymour, Spirkl, "Caterpillars in Erdős-Hajnal", arXiv:1810.00811,
Conjecture 1.5 (1810.00811__00).

A graph G is H-free if it has no induced subgraph isomorphic to H.  Two disjoint sets of vertices
are anticomplete if there is no edge between them.  A graph H has the sparse strong EH-property if
there exists ε > 0 such that every H-free graph G with |V(G)| >= 2 has a vertex with at least
ε|V(G)| neighbours, or two anticomplete sets of at least ε|V(G)| vertices each.

Conjecture 1.5: a graph H has the sparse strong EH-property if and only if H is a forest.

Encoding.  Graphs are finite and simple.  The constant ε is a rational number between 0 and 1, which
is not a restriction, and the inequalities are multiplied by its denominator. *)

From GraphTheory Require Import digraph sgraph.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

(** [A] and [B] are disjoint and there is no edge between them. *)
Definition anticomplete (G : sgraph) (A B : {set G}) : bool :=
  [disjoint A & B] && ~~ neighbor A B.

(** [G] has an induced subgraph isomorphic to [H]. *)
Definition has_induced_copy (G H : sgraph) : Prop := inhabited (H ⇀ G).

(** [G] has no induced subgraph isomorphic to [H]. *)
Definition induced_free (G H : sgraph) : Prop := ~ has_induced_copy G H.

(** ** Definitions copied from GraphLib/extremal.v *)

(** [H] has the sparse strong Erdős-Hajnal property: for some [eps > 0], each graph with at
    least two vertices and no induced [H] has a vertex of degree at least [eps |G|], or two
    anticomplete sets of size at least [eps |G|]. *)
Definition sparse_strong_EH (H : sgraph) : Prop :=
  exists eps_num eps_den : nat,
    0 < eps_num /\ eps_num <= eps_den /\
    forall G : sgraph,
      2 <= #|G| ->
      induced_free G H ->
      (exists v : G, eps_num * #|G| <= eps_den * #|N(v)|) \/
      (exists A B : {set G},
        anticomplete A B /\
        eps_num * #|G| <= eps_den * #|A| /\
        eps_num * #|G| <= eps_den * #|B|).

(** ** Statement *)

Definition AX_sparse_strong_erdos_hajnal_forests : Prop :=
  forall H : sgraph, sparse_strong_EH H <-> is_forest [set: H].
