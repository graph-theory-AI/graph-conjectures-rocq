(** * The Matthews–Sumner conjecture

Matthews, Sumner; Bondy, Murty, "Graph Theory", Appendix A, problem 79.

A graph is claw-free if it has no induced subgraph isomorphic to the claw K_1,3.

Conjecture: every 4-connected claw-free graph is Hamiltonian.

Encoding.  Graphs are finite and simple.  A 4-connected graph has more than four vertices. *)

From GraphTheory Require Import digraph sgraph connectivity.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

(** [G] has an induced subgraph isomorphic to [H]. *)
Definition has_induced_copy (G H : sgraph) : Prop := inhabited (H ⇀ G).

(** [G] has no induced subgraph isomorphic to [H]. *)
Definition induced_free (G H : sgraph) : Prop := ~ has_induced_copy G H.

(** [G] has no induced claw ([K_1,3]). *)
Definition claw_free (G : sgraph) : Prop := induced_free G 'K_1,3.

(** ** Definitions copied from GraphLib/hamiltonicity.v *)

(** [c] is a Hamiltonian cycle of [G]. *)
Definition hamiltonian_cycle (G : sgraph) (c : seq G) : bool :=
  ucycleb (--) c && (size c == #|G|).
Arguments hamiltonian_cycle : clear implicits.

(** [G] is Hamiltonian. *)
Definition hamiltonian (G : sgraph) : Prop :=
  exists c : seq G, hamiltonian_cycle G c.

(** ** Statement *)

Definition BM_matthews_sumner_4_connected_claw_free_hamiltonian : Prop :=
  forall G : sgraph, 4.-connected G -> claw_free G -> hamiltonian G.
