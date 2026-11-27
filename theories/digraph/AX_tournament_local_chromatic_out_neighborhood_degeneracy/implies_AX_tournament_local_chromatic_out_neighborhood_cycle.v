(** * Out-neighbourhoods of large degeneracy contain cycles

The degeneracy version of "chromatic number is not tournament-local" implies the cycle version.
Take d = 2: some out-neighbourhood W induces a subgraph that is not 1-degenerate, that is, W has
a nonempty subset S in which every vertex has at least two neighbours.  A longest path in S
starting at a vertex w has all the neighbours of w in S on it, and a neighbour other than the
second vertex of the path closes a cycle with at least three vertices.

The implication is the edge e020 of relations.json in graph-conjectures.  It was formalized in
graph-theory-rocq (digraph-theory/theories/conjectures/implications_X2.v). *)

From GraphTheory Require Import digraph sgraph.
From mathcomp Require Import boot.
From GC.GraphLib Require Import misc cycle.
From GC.digraph.AX_tournament_local_chromatic_out_neighborhood_degeneracy Require Import
  main(AX_tournament_local_chromatic_out_neighborhood_degeneracy).
From GC.digraph.AX_tournament_local_chromatic_out_neighborhood_cycle Require Import
  main(AX_tournament_local_chromatic_out_neighborhood_cycle).

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Theorem AX_tournament_local_chromatic_out_neighborhood_degeneracy_implies_AX_tournament_local_chromatic_out_neighborhood_cycle :
  AX_tournament_local_chromatic_out_neighborhood_degeneracy ->
  AX_tournament_local_chromatic_out_neighborhood_cycle.
Proof.
move=> H; have [C HC] := H 2; exists C => G r tour chiC.
have [v Hv] := HC G r tour chiC; exists v; set W := [set w | r v w].
have [/existsP[S /and3P[SW S0 /forall_inP degS]]|/existsPn noS] :=
  boolP [exists S : {set G}, [&& S \subset W, S != set0 & [forall x in S, 1 < #|N(x) :&: S|]]].
  have [c [cyc cS]] := min_degree2_seq_cycle S0 degS.
  by exists c; split=> // z /cS; apply/subsetP.
suff /Hv : degenerate_on W 1 by [].
move=> S SW S0; have := noS S; rewrite SW S0 /= => /forall_inPn[x xS].
by rewrite -leqNgt; exists x.
Qed.

Check (AX_tournament_local_chromatic_out_neighborhood_degeneracy_implies_AX_tournament_local_chromatic_out_neighborhood_cycle :
  GC.digraph.AX_tournament_local_chromatic_out_neighborhood_degeneracy.main.AX_tournament_local_chromatic_out_neighborhood_degeneracy ->
  GC.digraph.AX_tournament_local_chromatic_out_neighborhood_cycle.main.AX_tournament_local_chromatic_out_neighborhood_cycle).
Print Assumptions AX_tournament_local_chromatic_out_neighborhood_degeneracy_implies_AX_tournament_local_chromatic_out_neighborhood_cycle.
