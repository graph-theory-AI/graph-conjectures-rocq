(** * Hamiltonian cycles in line graphs

Thomassen, "Reflections on graph theory", J. Graph Theory 10 (1986); Open Problem Garden,
hamiltonian_cycles_in_line_graphs.

Conjecture: every 4-connected line graph is Hamiltonian.

Encoding.  Graphs are finite, and the line graphs are those of simple graphs.  A 4-connected graph
has more than four vertices. *)

From GraphTheory Require Import digraph sgraph connectivity.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

Section SimpleLineGraph.
Variable G : sgraph.

(** The edges of [G]. *)
Definition simple_line_vertex : Type := {e : {set G} | e \in E(G)}.

(** Distinct edges with a common end. *)
Definition simple_line_rel : rel simple_line_vertex :=
  fun e f => (val e != val f) && (val e :&: val f != set0).

Lemma simple_line_sym : symmetric simple_line_rel.
Proof. by move=> e f; rewrite /simple_line_rel eq_sym setIC. Qed.

Lemma simple_line_irrefl : irreflexive simple_line_rel.
Proof. by move=> e; rewrite /simple_line_rel eqxx. Qed.

(** The line graph of the simple graph [G]. *)
Definition simple_line_graph : sgraph := SGraph simple_line_sym simple_line_irrefl.

End SimpleLineGraph.

(** ** Definitions copied from GraphLib/hamiltonicity.v *)

(** [c] is a Hamiltonian cycle of [G]. *)
Definition hamiltonian_cycle (G : sgraph) (c : seq G) : bool :=
  ucycleb (--) c && (size c == #|G|).
Arguments hamiltonian_cycle : clear implicits.

(** [G] is Hamiltonian. *)
Definition hamiltonian (G : sgraph) : Prop :=
  exists c : seq G, hamiltonian_cycle G c.

(** ** Statement *)

Definition OPG_thomassen_4_connected_line_graphs_hamiltonian : Prop :=
  forall G : sgraph, 4.-connected (simple_line_graph G) -> hamiltonian (simple_line_graph G).
