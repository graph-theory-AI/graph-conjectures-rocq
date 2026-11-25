(** * Half-integral flow polynomial values

Mohar; Open Problem Garden, half_integral_flow_polynomial_values.

The flow polynomial Φ(G,x) of a graph G is the polynomial whose value Φ(G,k) is, for every positive
integer k, the number of nowhere-zero flows of G with values in the integers modulo k.

Conjecture: Φ(G,5.5) > 0 for every 2-edge-connected graph G.

Encoding.  Graphs are finite multigraphs, with loops and parallel edges, and with at least one
vertex.  They are 2-edge-connected if they are connected and have no bridge; a single vertex is
allowed.  The flow polynomial is defined by the formula
Φ(G,x) = Σ_S (-1)^(|E| - |S|) x^(|S| + c(S) - |V|), where S ranges over the sets of edges and c(S)
is the number of components of the spanning subgraph with edge set S. *)

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

(** [G] is [k]-edge-connected: it remains connected when fewer than [k] edges are deleted. *)
Definition medge_connected (G : mgraph) (k : nat) : Prop :=
  forall E : {set edge G}, #|E| < k -> connected [set: skeleton.skeleton (remove_edges E)].

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

Definition OPG_flow_polynomial_positive_at_5_5 : Prop :=
  forall G : mgraph,
    0 < #|G| -> medge_connected G 2 ->
    (0 < (map_poly intr (flow_poly G)).[11%:R / 2%:R : rat])%R.
