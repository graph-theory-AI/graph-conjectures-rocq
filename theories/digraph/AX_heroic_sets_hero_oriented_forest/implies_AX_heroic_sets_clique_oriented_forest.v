(** * The hero dichotomy for oriented forests implies the clique version

Let F be an oriented forest and k an integer.  The transitive tournament TT_(k+1) is a hero (here
K_1 joined k times to K_1), so by the hero dichotomy the oriented digraphs without induced copy of
TT_(k+1) and of F have bounded dichromatic number.  An induced copy of a tournament on k + 1
vertices is a clique of size k + 1 in the underlying graph, hence the digraphs of the clique version
(clique number less than k) lie in this class.

The implication is the edge e104 of relations.json in graph-conjectures.  It was formalized in
graph-theory-rocq (digraph-theory/theories/conjectures/implications_X1.v). *)

From GraphTheory Require Import preliminaries sgraph coloring digraph.
From mathcomp Require Import boot.
From GC.digraph.AX_heroic_sets_hero_oriented_forest Require Import
  main(AX_heroic_sets_hero_oriented_forest).
From GC.digraph.AX_heroic_sets_clique_oriented_forest Require Import
  main(AX_heroic_sets_clique_oriented_forest).

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Abbreviation hero := GC.digraph.AX_heroic_sets_hero_oriented_forest.main.hero.
Abbreviation digraph_join := GC.digraph.AX_heroic_sets_hero_oriented_forest.main.digraph_join.
Abbreviation transitive_tournament :=
  GC.digraph.AX_heroic_sets_hero_oriented_forest.main.transitive_tournament.
Abbreviation is_transitive_tournament :=
  GC.digraph.AX_heroic_sets_hero_oriented_forest.main.is_transitive_tournament.
Abbreviation tournament := GC.digraph.AX_heroic_sets_hero_oriented_forest.main.tournament.
Abbreviation underlying := GC.digraph.AX_heroic_sets_clique_oriented_forest.main.underlying.
Abbreviation hero_K1 := GC.digraph.AX_heroic_sets_hero_oriented_forest.main.hero_K1.
Abbreviation hero_join := GC.digraph.AX_heroic_sets_hero_oriented_forest.main.hero_join.

(** The join of two transitive tournaments is a transitive tournament. *)
Lemma transitive_tournament_join (D1 D2 : diGraph) :
  is_transitive_tournament D1 -> is_transitive_tournament D2 ->
  is_transitive_tournament (digraph_join D1 D2).
Proof.
move=> [[irr1 tot1] tr1] [[irr2 tot2] tr2]; split; first split.
- by case=> u /=; [exact: irr1 | exact: irr2].
- by case=> u [] v //=; [exact: tot1 | exact: tot2].
- by case=> y [] x [] z //=; [exact: tr1 | exact: tr2].
Qed.

(** For every [k], a hero that is a transitive tournament on [k.+1] vertices. *)
Lemma transitive_tournament_hero (k : nat) :
  exists H : diGraph, [/\ hero H, is_transitive_tournament H & #|H| = k.+1].
Proof.
have tt1 : is_transitive_tournament (transitive_tournament 1).
  split; first split; rewrite /edge_rel /=; [exact: ltnn | | exact: ltn_trans].
  by move=> u v; rewrite !ord1 eqxx ltnn.
elim: k => [|k [H [hH tH cH]]].
  by exists (transitive_tournament 1); split; [exact: hero_K1 | | exact: card_ord].
exists (digraph_join H (transitive_tournament 1)); split.
- exact: hero_join hH hero_K1.
- exact: transitive_tournament_join.
- by rewrite card_sum cH card_ord addn1.
Qed.

(** An induced copy of a tournament [H] in [D] is a clique of size [#|H|] of the underlying graph
    of [D]. *)
Lemma tournament_isubgraph_omega (H D : diGraph) :
  tournament H -> H ⇀ D -> #|H| <= ω([set: underlying D]).
Proof.
move=> [_ tot] f; rewrite -(card_imset _ (isubgraph_inj f)); apply: clique_bound.
rewrite inE subsetT; apply/cliqueP => _ _ /imsetP[x _ ->] /imsetP[y _ ->] fxy.
rewrite /edge_rel /= fxy /sc /= !isubgraph_mono.
by rewrite (inj_eq (isubgraph_inj f)) tot in fxy; case: (x -- y) (y -- x) fxy => [] [].
Qed.

Theorem AX_heroic_sets_hero_oriented_forest_implies_AX_heroic_sets_clique_oriented_forest :
  AX_heroic_sets_hero_oriented_forest -> AX_heroic_sets_clique_oriented_forest.
Proof.
move=> hd F k oF fF; have [H [hH tH cH]] := transitive_tournament_hero k.
have [B bnd] := (hd H F hH oF fF).2 (or_intror tH).
exists B => D [oD om nF]; apply: bnd; split=> // -[f].
have := tournament_isubgraph_omega tH.1 f; rewrite cH => /ltnW.
by rewrite leqNgt om.
Qed.

Check (AX_heroic_sets_hero_oriented_forest_implies_AX_heroic_sets_clique_oriented_forest :
  GC.digraph.AX_heroic_sets_hero_oriented_forest.main.AX_heroic_sets_hero_oriented_forest ->
  GC.digraph.AX_heroic_sets_clique_oriented_forest.main.AX_heroic_sets_clique_oriented_forest).

Print Assumptions
  AX_heroic_sets_hero_oriented_forest_implies_AX_heroic_sets_clique_oriented_forest.
