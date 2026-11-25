(** * Decomposition of even tournaments into directed paths

Alspach, Mason, Pullman, "Path numbers of tournaments", J. Combin. Theory Ser. B 20 (1976); Open
Problem Garden, decomposing_an_even_tournament_in_directed_paths.

Conjecture: the arcs of every tournament D on an even number of vertices can be partitioned into
Σ_v max{0, d^+(v) - d^-(v)} directed paths.

Encoding.  Digraphs are those of GraphTheory ([diGraph]): a finite type of vertices with a boolean
relation [--].  A directed path is a pair (x, s), where x is its first vertex and s the sequence of
its other vertices.  In a decomposition, each pair of vertices is used by one path if it is an arc,
and by none otherwise.  Paths without arc are allowed, which changes nothing: no decomposition has
fewer paths than the sum above.  The subtraction of natural numbers is truncated at 0. *)

From GraphTheory Require Import digraph.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

Section Paths.
Variable G : diGraph.
Implicit Types (p : seq G).

(** [p] is a path (nonempty, without repetition). *)
Definition seq_simple_path p : bool := if p is x :: q then path (--) x q && uniq p else false.

End Paths.

(** ** Definitions copied from GraphLib/digraph.v *)

(** [D] is a tournament: it has no loop, and exactly one arc between any two distinct vertices. *)
Definition tournament (D : diGraph) : Prop :=
  irreflexive (@edge_rel D) /\ forall x y : D, (x != y) = (x -- y) (+) (y -- x).

(** Out-degree. *)
Definition outdeg (D : diGraph) (v : D) : nat := #|N(v)|.

(** In-degree. *)
Definition indeg (D : diGraph) (v : D) : nat := #|[set u | u -- v]|.

(** The vertices [x :: s] form a directed path (from [x] to [last x s], of length [size s]). *)
Definition dipath (D : diGraph) (x : D) (s : seq D) : bool := seq_simple_path (x :: s).

(** The arcs of the directed path [x :: s]. *)
Definition dipath_arcs (D : diGraph) (x : D) (s : seq D) : {set D * D} :=
  [set p in zip (x :: s) s].

(** ** Statement *)

Definition OPG_even_tournament_directed_path_decomposition : Prop :=
  forall T : diGraph, tournament T -> ~~ odd #|T| ->
    exists Q : seq (T * seq T),
      [/\ all (fun p => dipath p.1 p.2) Q,
          [forall e : T * T, \sum_(p <- Q) (e \in dipath_arcs p.1 p.2) == (e.1 -- e.2)] &
          size Q = \sum_(v : T) (outdeg v - indeg v)].
