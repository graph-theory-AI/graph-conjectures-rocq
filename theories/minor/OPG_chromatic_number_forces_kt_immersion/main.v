(** * Chromatic number and immersions of complete graphs

Abu-Khzam, Langston, "Graph coloring and the immersion order"; Open Problem Garden,
coloring_and_immersion.

A graph G immerses a graph H if a graph isomorphic to H can be obtained from G by deleting vertices
and edges, and by splits: replacing two edges uv and vw by an edge uw.  Equivalently, the vertices
of H are mapped to distinct vertices of G, and the edges of H to pairwise edge-disjoint paths of G
between the images of their ends.

Conjecture: for every positive integer t, every (loopless) graph G with χ(G) >= t immerses K_t.

Encoding.  Graphs are finite and simple.  The edges of H are mapped to edge-disjoint walks, which is
equivalent.  There is one walk for each direction of each edge, and no condition between the two
walks of a same edge. *)

From GraphTheory Require Import digraph sgraph coloring.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

Section Sequences.
Variable T : finType.
Implicit Types s : seq T.

(** The list of the pairs of consecutive elements of [s]: the edges of a walk. *)
Definition seq_edge_list s : seq {set T} :=
  map (fun e : T * T => [set e.1; e.2]) (zip s (behead s)).

(** The set of the pairs of consecutive elements of [s]: the edge set of a walk. *)
Definition seq_edge_set s : {set {set T}} := [set e in seq_edge_list s].

End Sequences.

(** ** Definitions copied from GraphLib/minor.v *)

(** [G] contains an immersion of [H]: [f] maps the vertices of [H] to distinct vertices of [G],
    and the edges [u v] of [H] are mapped to pairwise edge-disjoint walks from [f u] to [f v]. *)
Definition immersion (G H : sgraph) : Prop :=
  exists (f : H -> G) (P : H -> H -> seq G),
    injective f /\
    (forall u v : H, u -- v ->
        path sedge (f u) (P u v) /\ last (f u) (P u v) = f v) /\
    (forall u1 v1 u2 v2 : H, u1 -- v1 -> u2 -- v2 ->
        [set u1; v1] != [set u2; v2] ->
        [disjoint seq_edge_set (f u1 :: P u1 v1)
                & seq_edge_set (f u2 :: P u2 v2)]).

(** ** Statement *)

Definition OPG_chromatic_number_forces_kt_immersion : Prop :=
  forall (t : nat) (G : sgraph),
    0 < t -> t <= χ([set: G]) -> immersion G 'K_t.
