(** * Clustered and defective colourings of graphs without odd minor

Hickingbotham, Kang, Oum, Steiner, Wood, "Clustered colouring of odd-H-minor-free graphs",
arXiv:2308.15721, Conjecture 2 (2308.15721__00).

The clustered chromatic number χ_*(F) of a class F of graphs is the minimum k such that, for some c,
every graph of F has a colouring with k colours whose monochromatic components have at most c
vertices.  The defective chromatic number χ_Δ(F) is the minimum k such that, for some m, every graph
of F has a colouring with k colours whose monochromatic components have maximum degree at most m.

H is an odd minor of G if there are disjoint subtrees T_x of G, x in V(H), and for each edge xy of H
an edge of G between T_x and T_y, such that some 2-colouring of these trees is proper on each T_x
and makes each of these edges monochromatic.  The connected tree-depth ctd(H) is the minimum number
of vertices of a longest path from the root in a rooted tree T on V(H) such that each edge of H
joins an ancestor and a descendant in T.

Conjecture: for every graph H, the class F of the graphs that do not have H as an odd minor
satisfies χ_*(F) <= 2 ctd(H) - 2 and χ_Δ(F) = ctd(H) - 1.

Encoding.  Graphs are finite and simple.  The trees T_x are replaced by their sets of vertices,
connected by edges with ends of different colours.  ctd(H) <= k means that k > 0 and that, for some
vertex r (the root), H - r has tree-depth at most k - 1, which is expressed by a vertex ranking.
The graph H has at least one vertex: otherwise, ctd(H) <= k never holds. *)

From GraphTheory Require Import digraph sgraph.
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

(** The defective chromatic number of the class [F] is at most [k]: its graphs have colourings
    with [k] colours whose monochromatic subgraphs have bounded maximum degree. *)
Definition defective_chromatic_le (F : sgraph -> Prop) (k : nat) : Prop :=
  exists m : nat,
    forall G : sgraph, F G ->
      exists col : G -> 'I_k,
        forall v : G, #|N(v) :&: [set u : G | col u == col v]| <= m.

(** ** Definitions copied from GraphLib/minor.v *)

(** [H] is an odd minor of [G]: for some 2-colouring [sigma] of the vertices of [G], it has a
    model in which the branch sets are connected by bichromatic edges, and the edges of [H] are
    realised by monochromatic edges. *)
Definition odd_minor (G H : sgraph) : Prop :=
  exists (B : H -> {set G}) (sigma : G -> bool),
    [/\ forall x : H, B x != set0,
        forall (x : H) (u v : G), u \in B x -> v \in B x ->
          connect (fun a b : G => [&& a \in B x, b \in B x, a -- b & sigma a != sigma b]) u v,
        forall x y : H, x != y -> [disjoint B x & B y] &
        forall x y : H, x -- y ->
          exists u v : G, [/\ u \in B x, v \in B y, u -- v & sigma u == sigma v]].

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

Definition AX_odd_minor_free_clustered_chromatic_treedepth : Prop :=
  forall (H : sgraph) (k : nat),
    connected_treedepth_le H k ->
    ~ connected_treedepth_le H k.-1 ->
    clustered_chromatic_le (fun G : sgraph => ~ odd_minor G H) (2 * k - 2) /\
    defective_chromatic_le (fun G : sgraph => ~ odd_minor G H) (k - 1) /\
    (forall j : nat, j.+1 < k ->
       ~ defective_chromatic_le (fun G : sgraph => ~ odd_minor G H) j).
