(** * Chvátal's toughness conjecture

Chvátal; Bondy, Murty, "Graph Theory", Appendix A, problem 89.

A connected graph G is k-tough if c(G - S) <= |S| / k for every vertex cut S of G, where c is the
number of components.  In particular complete graphs are k-tough for all k.

Conjecture: there exists a positive integer k such that every k-tough graph is Hamiltonian.

Encoding.  Graphs are finite and simple, with at least three vertices (the graph with one vertex is
k-tough for all k, but has no Hamilton cycle).  Vertex cuts are the sets S such that G - S has at
least two components; as k >= 1, the case where S is empty says that G is connected. *)

From GraphTheory Require Import digraph sgraph.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/hamiltonicity.v *)

(** [c] is a Hamiltonian cycle of [G]. *)
Definition hamiltonian_cycle (G : sgraph) (c : seq G) : bool :=
  ucycleb (--) c && (size c == #|G|).
Arguments hamiltonian_cycle : clear implicits.

(** [G] is Hamiltonian. *)
Definition hamiltonian (G : sgraph) : Prop :=
  exists c : seq G, hamiltonian_cycle G c.

(** [G] is [k]-tough: if the deletion of [S] leaves at least two components, there are at most
    [#|S| / k] of them. *)
Definition tough (G : sgraph) (k : nat) : Prop :=
  forall S : {set G},
    1 < #|components (~: S)| -> k * #|components (~: S)| <= #|S|.

(** ** Statement *)

Definition BM_chvatal_toughness_k_tough_hamiltonian : Prop :=
  exists k : nat,
    0 < k /\ forall G : sgraph, 2 < #|G| -> tough G k -> hamiltonian G.
