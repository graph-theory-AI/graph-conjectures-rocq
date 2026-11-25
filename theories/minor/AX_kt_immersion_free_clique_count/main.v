(** * Number of cliques in graphs without K_t immersion

Fox, Wei, "On the number of cliques in graphs with a forbidden subdivision or immersion",
arXiv:1606.06810, conjecture (1606.06810__00).

A (weak) immersion of a graph H in a graph G maps the vertices of H to distinct vertices of G, and
the edges of H to pairwise edge-disjoint paths of G between the images of their ends.  The cliques
are all the complete subgraphs, including the empty one.

Conjecture: the maximum number of cliques in a graph on n >= t - 2 vertices with no K_t immersion is
2^(t-2) (n - t + 3).

Encoding.  Graphs are finite and simple, and t >= 2.  The source does not specify weak or strong
immersions; we take weak ones.  The edges of H are mapped to edge-disjoint walks, which is
equivalent.  There is one walk for each direction of each edge, and no condition between the two
walks of a same edge.  The maximum is stated as an upper bound that is attained.  The subtraction in
n - t + 3 is done last, as subtraction is truncated. *)

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

Definition AX_kt_immersion_free_clique_count : Prop :=
  forall t n : nat,
    2 <= t ->
    t - 2 <= n ->
    (forall G : sgraph,
        #|G| = n ->
        ~ immersion G 'K_t ->
        #|cliques [set: G]| <= 2 ^ (t - 2) * (n + 3 - t)) /\
    (exists G : sgraph,
        #|G| = n /\
        ~ immersion G 'K_t /\
        #|cliques [set: G]| = 2 ^ (t - 2) * (n + 3 - t)).
