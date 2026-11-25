(** * Hamiltonian vertex-transitive graphs

Thomassen; Bondy, Murty, "Graph Theory", Appendix A, problem 88.

A graph is vertex-transitive if any vertex is mapped to any other by some automorphism.

Conjecture: all but finitely many connected vertex-transitive graphs are Hamiltonian.

Encoding.  Graphs are finite and simple.  As there are finitely many graphs on n vertices up to
isomorphism, "all but finitely many" means "all those with at least n_0 vertices, for some n_0".
The convention for graphs with at most two vertices does not matter. *)

From GraphTheory Require Import digraph sgraph.
From mathcomp Require Import boot perm.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/digraph.v *)

(** The automorphisms of [D]. *)
Definition automorphisms (D : diGraph) : {set {perm D}} :=
  [set p : {perm D} | [forall u : D, [forall v : D, (p u -- p v) == (u -- v)]]].

(** [D] is vertex-transitive. *)
Definition vertex_transitive (D : diGraph) : bool :=
  [forall u : D, [forall v : D, [exists p : {perm D}, (p \in automorphisms D) && (p u == v)]]].

(** ** Definitions copied from GraphLib/hamiltonicity.v *)

(** [c] is a Hamiltonian cycle of [G]. *)
Definition hamiltonian_cycle (G : sgraph) (c : seq G) : bool :=
  ucycleb (--) c && (size c == #|G|).
Arguments hamiltonian_cycle : clear implicits.

(** [G] is Hamiltonian. *)
Definition hamiltonian (G : sgraph) : Prop :=
  exists c : seq G, hamiltonian_cycle G c.

(** ** Statement *)

Definition BM_thomassen_vertex_transitive_finitely_many_non_hamiltonian : Prop :=
  exists n0 : nat,
    forall G : sgraph,
      n0 <= #|G| -> connected [set: G] -> vertex_transitive G -> hamiltonian G.
