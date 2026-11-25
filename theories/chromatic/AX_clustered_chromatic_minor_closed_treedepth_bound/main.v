(** * Clustered chromatic number and connected tree-depth

Norin, Scott, Seymour, Wood, "Clustered colouring in minor-closed classes", Combinatorica 39
(2019), arXiv:1708.02370, Conjecture 4 (1708.02370__00).

A colouring of the vertices of a graph has clustering c if every monochromatic component (component
of the subgraph induced by a colour) has at most c vertices.  The clustered chromatic number
χ_*(F) of a class F of graphs is the least k such that, for some integer c, every graph of F has a
colouring with k colours and clustering c.  M_H is the class of the graphs without minor H.  The
closure of a rooted tree is obtained by adding an edge between every ancestor and descendant, and
its depth is the maximum number of vertices on a path from the root to a leaf.  The connected
tree-depth ctd(H) is the minimum depth of a rooted tree whose closure contains H as a subgraph.

Conjecture 4: χ_*(M_H) <= 2 ctd(H) - 2 for every graph H.

Encoding.  Graphs are finite and simple.  H has connected tree-depth at most k if k >= 1 and H has
a vertex r such that H - r has tree-depth at most k-1 (r is the root of the tree).  The tree-depth
is at most k if there is a ranking of the vertices by k integers such that any walk between two
distinct vertices of the same rank contains a vertex of larger rank.  The bound is stated as
χ_*(M_H) <= 2k - 2 for every k >= ctd(H).  The graph H without vertices is excluded, as it has no
vertex r. *)

From GraphTheory Require Import digraph sgraph minor.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/chromatic.v *)

(** All elements of [S] have the same colour. *)
Definition monochromatic_on (T : finType) (C : eqType)
    (col : T -> C) (S : {set T}) : bool :=
  constant [seq col x | x <- enum S].

(** [G] has a colouring with [k] colours whose monochromatic components have at most [c]
    vertices. *)
Definition clustered_colorable (G : sgraph) (k c : nat) : Prop :=
  exists col : G -> 'I_k,
    forall S : {set G},
      connected S -> monochromatic_on col S -> #|S| <= c.

(** The clustered chromatic number of the class [F] is at most [k]: its graphs have colourings
    with [k] colours whose monochromatic components are bounded. *)
Definition clustered_chromatic_le (F : sgraph -> Prop) (k : nat) : Prop :=
  exists c : nat, forall G : sgraph, F G -> clustered_colorable G k c.

(** ** Definitions copied from GraphLib/minor.v *)

(** [rank] is a vertex ranking: each walk between distinct vertices of the same rank contains a
    vertex of larger rank. *)
Definition vertex_ranking (G : sgraph) (k : nat) (rank : G -> 'I_k) : Prop :=
  forall (x y : G) (p : seq G),
    x != y ->
    path (--) x p ->
    last x p = y ->
    rank x = rank y ->
    exists z : G, z \in p /\ rank x < rank z.

(** The tree-depth of [G] is at most [k]. *)
Definition treedepth_le (G : sgraph) (k : nat) : Prop :=
  exists rank : G -> 'I_k, vertex_ranking rank.

(** The connected tree-depth of [G] is at most [k]: [G] is a subgraph of the closure of a rooted
    tree of depth at most [k]. *)
Definition connected_treedepth_le (G : sgraph) (k : nat) : Prop :=
  0 < k /\ exists r : G, treedepth_le (induced (~: [set r])) k.-1.

(** ** Statement *)

Definition AX_clustered_chromatic_minor_closed_treedepth_bound : Prop :=
  forall (H : sgraph) (k : nat),
    connected_treedepth_le H k ->
    clustered_chromatic_le (fun G : sgraph => ~ minor G H) (2 * k - 2).
