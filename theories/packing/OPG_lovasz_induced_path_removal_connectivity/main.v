(** * Lovász path removal conjecture

Lovász; Open Problem Garden, lovasz_path_removal_conjecture.

A graph is k-connected if it has more than k vertices and no set of fewer than k vertices separates
two other vertices.

Conjecture: there is an integer-valued function f(k) such that, if G is any f(k)-connected graph and
x and y are any two vertices of G, then there is an induced path P with ends x and y such that
G - V(P) is k-connected.

Encoding.  Graphs are finite and simple, and the two vertices x and y are distinct.  An induced path
is a sequence of vertices. *)

From GraphTheory Require Import preliminaries digraph sgraph connectivity.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

Section Sequences.
Variable T : finType.
Implicit Types (s : seq T).

(** The list of the pairs of consecutive elements of [s]: the edges of a walk. *)
Definition seq_edge_list s : seq {set T} :=
  map (fun e : T * T => [set e.1; e.2]) (zip s (behead s)).

End Sequences.

Section InducedPathsCycles.
Variable G : sgraph.
Implicit Types (p : seq G) (a b u v : G).

(** [p] is an induced path (possibly empty): adjacent vertices of [p] are consecutive. *)
Definition chordless_path p : Prop :=
  [/\ uniq p, sorted (--) p
    & forall u v : G, u \in p -> v \in p -> u -- v -> [set u; v] \in seq_edge_list p].

(** [p] is an induced path from [a] to [b]. *)
Definition chordless_path_between a b p : Prop :=
  [/\ chordless_path p, ohead p = Some a & last a p = b].

End InducedPathsCycles.

(** ** Statement *)

Definition OPG_lovasz_induced_path_removal_connectivity : Prop :=
  exists f : nat -> nat,
    forall (k : nat) (G : sgraph) (x y : G),
      x != y -> (f k).-connected G ->
      exists p : seq G,
        chordless_path_between x y p /\ k.-connected (induced (~: [set:: p])).
