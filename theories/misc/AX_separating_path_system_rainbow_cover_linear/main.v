(** * Covering the edges by rainbow paths

Bonamy, Botler, Dross, Naia, Skokan, "Separating the edges of a graph by a linear number of
paths", arXiv:2301.08707, Problem 4 (2301.08707__01).

A path is rainbow if its edges have distinct colours.

Problem 4: does every properly edge-coloured graph G admit O(|V(G)|) rainbow paths that cover E(G)?

The proposition states the positive answer: there is a constant c such that every properly
edge-coloured graph G has at most c |V(G)| rainbow paths that cover E(G).

Encoding.  Paths are sequences of vertices, and the colours are the elements of an arbitrary finite
type. *)

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

End Sequences.

Section Paths.
Variable G : diGraph.
Implicit Types p : seq G.

(** [p] is a path (nonempty, without repetition). *)
Definition seq_simple_path p : bool := if p is x :: q then path (--) x q && uniq p else false.

End Paths.

(** ** Definitions copied from GraphLib/chromatic.v *)

(** [col] is a proper edge colouring. *)
Definition proper_edge_coloring (G : sgraph) (C : eqType) (col : {set G} -> C) : Prop :=
  forall x y z : G, x -- y -> x -- z -> y != z -> col [set x; y] != col [set x; z].

(** The path [p] is rainbow: its edges have distinct colours. *)
Definition rainbow_path
    (G : sgraph) (C : finType) (col : {set G} -> C) (p : seq G) : Prop :=
  seq_simple_path p /\ uniq (map col (seq_edge_list p)).

(** ** Definitions specific to the conjecture *)

(** Every edge of [G] is an edge of some path of the list [paths]. *)
Definition edges_covered_by_paths (G : sgraph) (paths : seq (seq G)) : Prop :=
  forall e : {set G},
    e \in E(G) -> exists p : seq G, p \in paths /\ e \in seq_edge_list p.

(** ** Statement *)

Definition AX_separating_path_system_rainbow_cover_linear : Prop :=
  exists c : nat,
    forall (G : sgraph) (C : finType) (col : {set G} -> C),
      proper_edge_coloring col ->
      exists paths : seq (seq G),
        size paths <= c * #|G| /\
        (forall p : seq G, p \in paths -> rainbow_path col p) /\
        edges_covered_by_paths paths.
