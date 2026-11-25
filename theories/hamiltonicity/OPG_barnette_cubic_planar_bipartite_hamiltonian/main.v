(** * Barnette's conjecture

Barnette, Conjecture 5 in "Recent progress in combinatorics" (ed. W. T. Tutte), Academic Press
(1969); Open Problem Garden, barnettes_conjecture.

Conjecture: every 3-connected cubic planar bipartite graph is Hamiltonian.

Encoding.  Graphs are finite and simple.  A 3-connected graph has more than three vertices.
Planarity is the absence of K_5 and K_3,3 minors (Wagner's theorem). *)

From GraphTheory Require Import digraph sgraph connectivity minor.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

(** Every vertex has degree [d]. *)
Definition regular (G : sgraph) (d : nat) : Prop := forall v : G, #|N(v)| = d.

(** [G] is bipartite: it has a bipartition (a set [A] such that each edge has exactly one end in
    [A]). *)
Definition bipartite (G : diGraph) : Prop := exists A : {set G}, bipartition A.

(** ** Definitions copied from GraphLib/hamiltonicity.v *)

(** [c] is a Hamiltonian cycle of [G]. *)
Definition hamiltonian_cycle (G : sgraph) (c : seq G) : bool :=
  ucycleb (--) c && (size c == #|G|).
Arguments hamiltonian_cycle : clear implicits.

(** [G] is Hamiltonian. *)
Definition hamiltonian (G : sgraph) : Prop :=
  exists c : seq G, hamiltonian_cycle G c.

(** ** Definitions copied from GraphLib/topological.v *)

(** [G] is planar: it has no minor [K_5] or [K_3,3]. *)
Definition planar (G : sgraph) : Prop :=
  ~ minor G 'K_5 /\ ~ minor G (KB 3 3).

(** ** Statement *)

Definition OPG_barnette_cubic_planar_bipartite_hamiltonian : Prop :=
  forall G : sgraph,
    planar G -> 3.-connected G -> regular G 3 -> bipartite G -> hamiltonian G.
