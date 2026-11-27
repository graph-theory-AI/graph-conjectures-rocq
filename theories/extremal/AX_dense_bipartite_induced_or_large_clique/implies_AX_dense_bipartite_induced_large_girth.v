(** * Dense bipartite induced subgraphs: from the clique dichotomy to graphs of large girth

Let x2 and x3 be the functions of the dichotomy, and d0 such that x2(d0) >= 3 and x3(d0) >= 3.
Take g0 = 4.  A graph of girth at least 4 has no clique on 3 vertices, hence a graph of girth at
least 4 and minimum degree at least d0 has a nonempty bipartite induced subgraph of minimum degree
at least x3(d0) >= 3.

The implication is the edge e075 of relations.json in graph-conjectures.  It was formalized in
graph-theory-rocq (extremal-graph-theory/theories/conjectures/implications_X13.v). *)

From GraphTheory Require Import digraph sgraph.
From mathcomp Require Import boot.
From GC.extremal.AX_dense_bipartite_induced_or_large_clique Require Import
  main(AX_dense_bipartite_induced_or_large_clique).
From GC.extremal.AX_dense_bipartite_induced_large_girth Require Import
  main(AX_dense_bipartite_induced_large_girth).
From GC.GraphLib Require Import cycle(girth_ge4_triangle_free).

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Theorem AX_dense_bipartite_induced_or_large_clique_implies_AX_dense_bipartite_induced_large_girth :
  AX_dense_bipartite_induced_or_large_clique -> AX_dense_bipartite_induced_large_girth.
Proof.
move=> [x2 [x3 [inf2 inf3 H]]]; have [[N2 x2N] [N3 x3N]] := (inf2 3, inf3 3).
exists (maxn N2 N3), 4 => G G0 g4 deg.
case: (H _ G G0 deg) => [[S [clS S3]]|[S [S0 bip degS]]].
  have /card_gt2P[x [y [z [[xS yS zS] [xy yz zx]]]]] := leq_trans (x2N _ (leq_maxl _ _)) S3.
  by exfalso; apply: (@girth_ge4_triangle_free _ g4 x y z); apply: clS.
by exists S; split=> // v; apply: leq_trans (x3N _ (leq_maxr _ _)) (degS v).
Qed.

Check (AX_dense_bipartite_induced_or_large_clique_implies_AX_dense_bipartite_induced_large_girth :
  GC.extremal.AX_dense_bipartite_induced_or_large_clique.main.AX_dense_bipartite_induced_or_large_clique ->
  GC.extremal.AX_dense_bipartite_induced_large_girth.main.AX_dense_bipartite_induced_large_girth).
Print Assumptions AX_dense_bipartite_induced_or_large_clique_implies_AX_dense_bipartite_induced_large_girth.
