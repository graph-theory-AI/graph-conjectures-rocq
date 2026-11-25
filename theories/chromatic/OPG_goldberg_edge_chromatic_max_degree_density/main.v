(** * Goldberg's conjecture

Goldberg, "Multigraphs with a chromatic index that is nearly maximal", Diskret. Analiz 23 (1973);
also Andersen and Seymour; Open Problem Garden, goldbergs_conjecture.

The edge chromatic number χ'(G) of a multigraph G is the minimum number of colours of a proper
colouring of its edges (distinct edges with a common end have different colours).  The overfull
parameter w(G) is the maximum of ⌈|E(H)| / ⌊|V(H)| / 2⌋⌉ for the subgraphs H of G with at least two
vertices.

Conjecture: every multigraph G satisfies χ'(G) <= max {Δ(G) + 1, w(G)}.

Encoding.  Multigraphs are finite and may have parallel edges and loops; a loop is counted once in
the degrees.  The subgraphs H are the induced ones, without loss of generality, and those with at
most one vertex count for 0.  χ'(G) is the chromatic number of the line graph. *)

From GraphTheory Require Import mgraph.
From GraphTheory Require Import digraph sgraph coloring.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

(** The ceiling of [a / b] (0 if [b = 0]). *)
Definition ceil_div (a b : nat) : nat := (a + b - 1) %/ b.

(** Multigraphs without labels. *)
Abbreviation mgraph := (graph unit unit).

(** The maximum number of edges incident to a vertex (a loop is counted once). *)
Definition mDelta (G : mgraph) : nat := \max_(v : G) #|edges_at v|.

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

(** ** Definitions copied from GraphLib/chromatic.v *)

(** The chromatic index of [G] ([0] for [G] without edges; loops are allowed). *)
Definition mchromatic_index (G : mgraph) : nat := χ([set: mline_graph G]).

(** The overfull parameter of [G]: the maximum of [|E(S)| / floor(|S| / 2)], rounded up, for the
    sets [S] of vertices (those with at most one vertex count for 0). *)
Definition overfull_parameter (G : mgraph) : nat :=
  \max_(S : {set G}) ceil_div #|edge_set S| (#|S| %/ 2).

(** ** Statement *)

Definition OPG_goldberg_edge_chromatic_max_degree_density : Prop :=
  forall G : mgraph,
    mchromatic_index G <= maxn (mDelta G).+1 (overfull_parameter G).
