(** * Real roots of the flow polynomial

Welsh; Open Problem Garden, real_roots_of_the_flow_polynomial.

The flow polynomial of a graph G is the polynomial whose value at every positive integer k is the
number of nowhere-zero flows of G with values in the integers modulo k.

Conjecture: all real roots of nonzero flow polynomials are at most 4.

Encoding.  Graphs are finite multigraphs, with loops and parallel edges.  The flow polynomial is
defined by the formula Σ_S (-1)^(|E| - |S|) x^(|S| + c(S) - |V|), where S ranges over the sets of
edges and c(S) is the number of components of the spanning subgraph with edge set S.  Its
coefficients are integers, and its roots are taken in an arbitrary real closed field. *)

From GraphTheory Require Import mgraph.
From GraphTheory Require Import digraph sgraph.
From GraphTheory Require skeleton.
From mathcomp Require Import boot algebra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Num.Theory.

(** ** Definitions copied from GraphLib/misc.v *)

(** Multigraphs without labels. *)
Abbreviation mgraph := (graph unit unit).

(** ** Definitions copied from GraphLib/cycle.v *)

Section FlowPolynomial.
Variable G : mgraph.
Local Open Scope ring_scope.

(** The number of components of the spanning subgraph with edge set [S]. *)
Definition component_count (S : {set edge G}) : nat :=
  #|components [set: skeleton.skeleton (remove_edges (~: S))]|.

(** The cyclomatic number of the spanning subgraph with edge set [S]. *)
Definition cyclomatic_number (S : {set edge G}) : nat :=
  (#|S| + component_count S - #|G|)%N.

(** The flow polynomial of [G]. *)
Definition flow_poly : {poly int} :=
  \sum_(S : {set edge G}) (-1) ^+ (#|edge G| - #|S|) *: 'X^(cyclomatic_number S).

End FlowPolynomial.

(** ** Statement *)

Definition OPG_flow_polynomial_real_roots_below_4 : Prop :=
  forall G : mgraph, flow_poly G != 0%R ->
    forall (F : rcfType) (z : F),
      root (map_poly (fun n : int => n%:~R%R : F) (flow_poly G)) z -> (z <= 4%:R)%R.
