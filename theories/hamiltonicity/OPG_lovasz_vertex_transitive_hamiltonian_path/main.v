(** * Hamiltonian paths in vertex-transitive graphs

Lovász, Problem 11 in "Combinatorial structures and their applications" (1970); Open Problem Garden,
hamiltonian_paths_and_cycles_in_vertex_transitive_graphs.

A graph is vertex-transitive if any vertex is mapped to any other by some automorphism.

Question: does every connected vertex-transitive graph have a Hamiltonian path?  What is stated is
the positive answer.

Encoding.  Graphs are finite, simple and nonempty.  Paths are sequences of vertices. *)

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

(** [s] is a Hamiltonian path of [G]. *)
Definition hamiltonian_path (G : sgraph) (s : seq G) : bool :=
  [&& sorted (--) s, uniq s & size s == #|G|].
Arguments hamiltonian_path : clear implicits.

(** [G] is traceable: it has a Hamiltonian path. *)
Definition traceable (G : sgraph) : Prop :=
  exists s : seq G, hamiltonian_path G s.

(** ** Statement *)

Definition OPG_lovasz_vertex_transitive_hamiltonian_path : Prop :=
  forall G : sgraph,
    0 < #|G| -> connected [set: G] -> vertex_transitive G -> traceable G.
