(** * Strongly separating path systems

Bonamy, Botler, Dross, Naia, Skokan, "Separating the edges of a graph by a linear number of
paths", arXiv:2301.08707, Problem 3 (2301.08707__00).

A collection P of paths of a graph G is a strongly separating path system if for any two distinct
edges e and f of G, some path of P contains e but not f, and some path of P contains f but not e.

Problem 3: does every graph on n vertices admit a strongly separating path system of size 2n?

The proposition states the positive answer.

Encoding.  The paths are sequences of vertices, and they are listed in a sequence P of length at
most 2n.  Paths with a single vertex are allowed, and useless. *)

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

(** ** Statement *)

Definition AX_separating_path_system_strong_2n : Prop :=
  forall G : sgraph, exists P : seq (seq G),
    [/\ size P <= 2 * #|G|,
        forall p : seq G, p \in P -> seq_simple_path p
      & forall e f : {set G}, e \in E(G) -> f \in E(G) -> e != f ->
          exists2 p : seq G, p \in P & (e \in seq_edge_set p) && (f \notin seq_edge_set p)].
