(** * Cantoni's conjecture

Cantoni; Bondy, Murty, "Graph Theory", Appendix A, problem 85.

Conjecture: every planar cubic graph with exactly three Hamilton cycles contains a triangle.

Encoding.  Graphs are finite and simple (the multigraph with two vertices and three parallel edges
is a trivial exception).  Planarity is the absence of K_5 and K_3,3 minors (Wagner's theorem).
Hamilton cycles are sequences of vertices, counted up to their edge sets. *)

From GraphTheory Require Import digraph sgraph minor.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

(** Every vertex has degree [d]. *)
Definition regular (G : sgraph) (d : nat) : Prop := forall v : G, #|N(v)| = d.

Section Sequences.
Variable T : finType.
Implicit Types c : seq T.

(** The list of the pairs of consecutive elements of the cyclic sequence [c]: the edges of a
    closed walk. *)
Definition seq_cycle_edge_list c : seq {set T} :=
  map (fun p : T * T => [set p.1; p.2]) (zip c (rot 1 c)).

(** The set of the pairs of consecutive elements of the cyclic sequence [c]: the edge set of the
    cycle [c]. *)
Definition seq_cycle_edge_set c : {set {set T}} := [set e in seq_cycle_edge_list c].

End Sequences.

(** ** Definitions copied from GraphLib/hamiltonicity.v *)

(** [c] is a Hamiltonian cycle of [G]. *)
Definition hamiltonian_cycle (G : sgraph) (c : seq G) : bool :=
  ucycleb (--) c && (size c == #|G|).
Arguments hamiltonian_cycle : clear implicits.

(** The set of the edge sets of the Hamiltonian cycles of [G]. *)
Definition hamiltonian_edge_sets (G : sgraph) : {set {set {set G}}} :=
  [set A : {set {set G}} |
    [exists c : (#|G|).-tuple G,
       hamiltonian_cycle G c && (A == seq_cycle_edge_set c)]].

(** ** Definitions copied from GraphLib/topological.v *)

(** [G] is planar: it has no minor [K_5] or [K_3,3]. *)
Definition planar (G : sgraph) : Prop :=
  ~ minor G 'K_5 /\ ~ minor G (KB 3 3).

(** ** Statement *)

Definition BM_cantoni_planar_cubic_three_hamilton_cycles_triangle : Prop :=
  forall G : sgraph,
    planar G -> regular G 3 -> #|hamiltonian_edge_sets G| = 3 ->
    exists x y z : G, [/\ x -- y, y -- z & z -- x].
