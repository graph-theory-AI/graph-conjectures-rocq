(** * Seymour's r-graph conjecture

Seymour, "On multicolourings of cubic graphs, and conjectures of Fulkerson and Tutte", Proc. London
Math. Soc. 38 (1979); Open Problem Garden, seymours_r_graph_conjecture.

The edge chromatic number χ'(G) of a multigraph G is the minimum number of colours of a proper
colouring of its edges (distinct edges with a common end have different colours).  An r-graph is an
r-regular multigraph G such that |δ(X)| >= r for every set X of vertices of odd size, where δ(X) is
the set of edges with exactly one end in X.

Conjecture: χ'(G) <= r + 1 for every r-graph G.

Encoding.  Multigraphs are finite and may have parallel edges; an r-graph has no loop, by the
condition on the sets of one vertex.  χ'(G) is the chromatic number of the line graph. *)

From GraphTheory Require Import mgraph.
From GraphTheory Require Import digraph sgraph coloring.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

(** Multigraphs without labels. *)
Abbreviation mgraph := (graph unit unit).

(** Every vertex is incident to [r] edges (a loop is counted once). *)
Definition mregular (G : mgraph) (r : nat) : Prop := forall v : G, #|edges_at v| = r.

(** Distinct edges with a common end. *)
Definition mline_rel (G : mgraph) : rel (edge G) :=
  fun e1 e2 => (e1 != e2) && [exists v : G, incident v e1 && incident v e2].

Lemma mline_rel_sym (G : mgraph) : symmetric (@mline_rel G).
Proof.
move=> e1 e2; rewrite /mline_rel eq_sym; congr (_ && _).
by apply/existsP/existsP=> -[v Hv]; exists v; rewrite andbC.
Qed.

Lemma mline_rel_irrefl (G : mgraph) : irreflexive (@mline_rel G).
Proof. by move=> e; rewrite /mline_rel eqxx. Qed.

(** The line graph of the multigraph [G] (parallel edges are adjacent). *)
Definition mline_graph (G : mgraph) : sgraph := SGraph (@mline_rel_sym G) (@mline_rel_irrefl G).

(** The edges with exactly one end in [S]. *)
Definition mcut (G : mgraph) (S : {set G}) : {set edge G} :=
  [set e | (source e \in S) (+) (target e \in S)].

(** ** Definitions copied from GraphLib/chromatic.v *)

(** The chromatic index of [G] ([0] for [G] without edges; loops are allowed). *)
Definition mchromatic_index (G : mgraph) : nat := χ([set: mline_graph G]).

(** [G] is an [r]-graph: it is [r]-regular, and each odd cut has at least [r] edges. *)
Definition r_graph (G : mgraph) (r : nat) : Prop :=
  mregular G r /\ (forall X : {set G}, odd #|X| -> r <= #|mcut X|).

(** ** Statement *)

Definition OPG_seymour_r_graph_edge_chromatic_r_plus_1 : Prop :=
  forall (r : nat) (G : mgraph), r_graph G r -> mchromatic_index G <= r.+1.
