(** * Path decompositions of graphs that are not odd semi-cliques

Bonamy, Perrett, "Gallai's path decomposition conjecture for graphs of small maximum degree",
arXiv:1609.06257, Question 1.1 (1609.06257__00).

A path decomposition of a graph G is a collection of paths of G such that each edge of G belongs to
exactly one of them.  An odd semi-clique is a graph obtained from a clique on 2k+1 vertices by
deleting at most k-1 edges, for some k >= 1.

Question: does every connected graph G that is not an odd semi-clique admit a path decomposition
into ⌊|V(G)| / 2⌋ paths?

The proposition states the positive answer.

Encoding.  Graphs are finite and simple.  Paths are sequences of vertices, and may be reduced to one
vertex, so that "⌊|V(G)| / 2⌋ paths" means at most ⌊|V(G)| / 2⌋ paths.  An odd semi-clique is
described as a graph with 2k+1 vertices whose complement has at most k-1 edges. *)

From GraphTheory Require Import digraph sgraph.
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

Section Paths.
Variable G : diGraph.
Implicit Types p : seq G.

(** [p] is a path (nonempty, without repetition). *)
Definition seq_simple_path p : bool := if p is x :: q then path (--) x q && uniq p else false.

End Paths.

(** ** Definitions copied from GraphLib/packing.v *)

(** The edges of [G] can be partitioned into at most [m] paths. *)
Definition path_number_le (G : sgraph) (m : nat) : Prop :=
  exists (r : nat) (P : 'I_r -> seq G),
    [/\ r <= m,
        (forall i : 'I_r, seq_simple_path (P i)),
        (forall i j : 'I_r,
            i != j ->
            [disjoint seq_edge_set (P i) & seq_edge_set (P j)])
      & \bigcup_(i : 'I_r) seq_edge_set (P i) = E(G)].

(** ** Definitions specific to the conjecture *)

(** [G] is an odd semi-clique. *)
Definition odd_semi_clique (G : sgraph) : Prop :=
  exists k : nat, [/\ 0 < k, #|G| = 2 * k + 1 & #|E(compl G)| <= k - 1].

(** ** Statement *)

Definition AX_gallai_path_decomposition_odd_semi_cliques : Prop :=
  forall G : sgraph,
    connected [set: G] -> ~ odd_semi_clique G -> path_number_le G (#|G| %/ 2).
