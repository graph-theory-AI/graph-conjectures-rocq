(** * Goldberg's conjecture implies Seymour's r-graph conjecture

Let G be an r-graph.  Its maximum degree is r, and its overfull parameter is at most r: an r-graph
has no loop (a loop at v would leave fewer than r edges in the cut of {v}), so for a set S of
vertices, counting the ends in S of the edges gives 2|E(S)| + |δ(S)| <= r|S|; as |δ(S)| >= r when
|S| is odd, |E(S)| <= r⌊|S|/2⌋.  Goldberg's bound max(Δ + 1, w) is thus at most r + 1.

The implication is classical (see Stiebitz, Scheide, Toft and Favrholdt, "Graph Edge Coloring",
2012), and is the edge e001 of relations.json in graph-conjectures.  It was formalized in
graph-theory-rocq (chromatic-theory/theories/conjectures/implications_U5.v). *)

From GraphTheory Require Import mgraph.
From mathcomp Require Import boot zify_ssreflect.
From GC.GraphLib Require Import misc(mgraph, mloopless, mcut, ceil_div).
From GC.GraphLib Require Import chromatic(r_graph).
From GC.chromatic.OPG_goldberg_edge_chromatic_max_degree_density Require Import
  main(OPG_goldberg_edge_chromatic_max_degree_density).
From GC.chromatic.OPG_seymour_r_graph_edge_chromatic_r_plus_1 Require Import
  main(OPG_seymour_r_graph_edge_chromatic_r_plus_1).

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** The ends of [e] are the vertices incident to [e]. *)
Lemma incidentE (G : mgraph) (v : G) (e : edge G) :
  incident v e = (v == source e) || (v == target e).
Proof. by apply/existsP/orP => [[[] /eqP<-]|[]/eqP->]; [right|left|exists false|exists true]. Qed.

(** Counting the ends in [S] of the edges of a loopless multigraph:
    [2 |E(S)| + |δ(S)|] is at most (in fact equal to) the sum of the degrees in [S]. *)
Lemma degree_sum_cut (G : mgraph) (S : {set G}) : mloopless G ->
  2 * #|edge_set S| + #|mcut S| <= \sum_(v in S) #|edges_at v|.
Proof.
move=> loopless.
have cardE (T : finType) (A : {set T}) : #|A| = \sum_x (x \in A : nat).
  by rewrite -sum1_card big_mkcond; apply: eq_bigr => x _; case: (x \in A).
under eq_bigr => v _ do rewrite cardE.
rewrite exchange_big !cardE big_distrr -big_split /=; apply: leq_sum => e _.
have -> : \sum_(v in S) (e \in edges_at v) = #|S :&: [set source e; target e]|.
  rewrite cardE big_mkcond; apply: eq_bigr => v _.
  by rewrite !inE incidentE; case: (v \in S).
have := loopless e.
rewrite !inE; case/boolP: (source e \in S); case/boolP: (target e \in S) => tS sS st /=.
- by rewrite (setIidPr _) ?cards2 ?st // subUset !sub1set sS tS.
- by apply/card_gt0P; exists (source e); rewrite !inE sS eqxx.
- by apply/card_gt0P; exists (target e); rewrite !inE tS eqxx orbT.
- by [].
Qed.

(** An [r]-graph has no loop: the cut of [{v}] has at least [r] edges, hence all the edges
    incident to [v]. *)
Lemma r_graph_loopless (G : mgraph) (r : nat) : r_graph G r -> mloopless G.
Proof.
move=> [reg cut] e; apply/negP => /eqP st.
have /eqP cutE : mcut [set source e] == edges_at (source e).
  rewrite eqEcard reg cut ?cards1 // andbT; apply/subsetP => f; rewrite !inE incidentE.
  by rewrite ![source e == _]eq_sym; case: (source f == _).
by move/setP/(_ e): cutE; rewrite !inE incidentE -st !eqxx.
Qed.

(** In an [r]-graph, [|E(S)| <= r ⌊|S|/2⌋]. *)
Lemma r_graph_edge_set (G : mgraph) (r : nat) (S : {set G}) :
  r_graph G r -> #|edge_set S| <= r * (#|S| %/ 2).
Proof.
move=> rG; have := degree_sum_cut S (r_graph_loopless rG); case: rG => reg cut.
rewrite (eq_bigr (fun _ => r)) // sum_nat_const {1}(divn_eq #|S| 2) modn2.
have : r * odd #|S| <= #|mcut S| by case/boolP: (odd #|S|) => [/cut|_]; rewrite ?muln1 ?muln0.
lia.
Qed.

(** [⌈a / q⌉ <= r] when [a <= r q]. *)
Lemma ceil_div_leq (a q r : nat) : a <= r * q -> ceil_div a q <= r.
Proof.
case: q => [|q] aq; first by rewrite /ceil_div divn0.
by rewrite /ceil_div -ltnS ltn_divLR // addnS subn1 /= mulSn addnC addSn ltnS leq_add2l.
Qed.

Theorem OPG_goldberg_edge_chromatic_max_degree_density_implies_OPG_seymour_r_graph_edge_chromatic_r_plus_1 :
  OPG_goldberg_edge_chromatic_max_degree_density -> OPG_seymour_r_graph_edge_chromatic_r_plus_1.
Proof.
move=> goldberg r G rG; apply: leq_trans (goldberg G) _; rewrite geq_max ltnS.
apply/andP; split; first by apply/bigmax_leqP => v _; rewrite rG.1.
apply/leqW/bigmax_leqP => S _; exact/ceil_div_leq/r_graph_edge_set.
Qed.

Check (OPG_goldberg_edge_chromatic_max_degree_density_implies_OPG_seymour_r_graph_edge_chromatic_r_plus_1 :
  GC.chromatic.OPG_goldberg_edge_chromatic_max_degree_density.main.OPG_goldberg_edge_chromatic_max_degree_density ->
  GC.chromatic.OPG_seymour_r_graph_edge_chromatic_r_plus_1.main.OPG_seymour_r_graph_edge_chromatic_r_plus_1).
Print Assumptions OPG_goldberg_edge_chromatic_max_degree_density_implies_OPG_seymour_r_graph_edge_chromatic_r_plus_1.
