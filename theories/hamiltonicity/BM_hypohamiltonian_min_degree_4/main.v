(** * Hypohamiltonian graphs of minimum degree at least 4

Thomassen; Bondy, Murty, "Graph Theory", Appendix A, problem 90.

A graph is hypohamiltonian if it is not Hamiltonian but every vertex-deleted subgraph is.

Question: is there a hypohamiltonian graph of minimum degree at least 4?

The proposition states the positive answer.

Encoding.  Graphs are finite and simple.  The empty graph satisfies the degree condition, but it is
Hamiltonian with the definition below.  Thus G has at least five vertices. *)

From GraphTheory Require Import digraph sgraph.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

(** Every vertex has degree at least [d] (true if [G] is empty). *)
Definition min_degree_ge (G : sgraph) (d : nat) : Prop := forall v : G, d <= #|N(v)|.

(** ** Definitions copied from GraphLib/hamiltonicity.v *)

(** [c] is a Hamiltonian cycle of [G]. *)
Definition hamiltonian_cycle (G : sgraph) (c : seq G) : bool :=
  ucycleb (--) c && (size c == #|G|).
Arguments hamiltonian_cycle : clear implicits.

(** [G] is Hamiltonian. *)
Definition hamiltonian (G : sgraph) : Prop :=
  exists c : seq G, hamiltonian_cycle G c.

(** [G] is hypohamiltonian: it is not Hamiltonian, but it is after the deletion of any vertex. *)
Definition hypohamiltonian (G : sgraph) : Prop :=
  ~ hamiltonian G /\ forall v : G, hamiltonian (induced [set~ v]).

(** ** Statement *)

Definition BM_hypohamiltonian_min_degree_4 : Prop :=
  exists G : sgraph, min_degree_ge G 4 /\ hypohamiltonian G.
