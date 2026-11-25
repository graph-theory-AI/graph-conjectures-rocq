(** * The 1-factorization conjecture

Hilton; Bondy, Murty, "Graph Theory", Appendix A, problem 57.

Conjecture: every simple d-regular graph on n vertices, with n even and d >= n/2, is
d-edge-colourable.

Encoding.  Graphs are finite and nonempty.  The condition d >= n/2 is written n <= 2d.  The
d-edge-colourability is expressed by the chromatic number of the line graph. *)

From GraphTheory Require Import digraph sgraph coloring.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

(** Every vertex has degree [d]. *)
Definition regular (G : sgraph) (d : nat) : Prop := forall v : G, #|N(v)| = d.

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

(** ** Statement *)

Definition BM_1_factorization_dense_regular_graphs : Prop :=
  forall (G : sgraph) (d : nat),
    0 < #|G| -> ~~ odd #|G| -> regular G d -> #|G| <= 2 * d ->
    χ([set: simple_line_graph G]) <= d.
