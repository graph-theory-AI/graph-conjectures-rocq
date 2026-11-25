(** * Regular graphs are not uniquely Hamiltonian

Sheehan, "The multiplicity of Hamiltonian circuits in a graph", Recent advances in graph theory
(1975); Open Problem Garden, uniquely_hamiltonian_graphs.

A graph is uniquely Hamiltonian if it contains exactly one Hamilton cycle.

Conjecture: if G is a finite r-regular graph, where r > 2, then G is not uniquely Hamiltonian.

Encoding.  Graphs are finite, simple and nonempty (the empty sequence would be the unique
Hamilton cycle of the empty graph).  Cycles are sequences of vertices, and two cycles are the same
if their edge sets are. *)

From GraphTheory Require Import digraph sgraph.
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

(** [G] is uniquely Hamiltonian: it has exactly one Hamiltonian cycle, up to its edge set. *)
Definition uniquely_hamiltonian (G : sgraph) : Prop :=
  #|hamiltonian_edge_sets G| = 1.

(** ** Statement *)

Definition OPG_regular_graphs_not_uniquely_hamiltonian : Prop :=
  forall (r : nat) (G : sgraph),
    0 < #|G| -> 2 < r -> regular G r -> ~ uniquely_hamiltonian G.
