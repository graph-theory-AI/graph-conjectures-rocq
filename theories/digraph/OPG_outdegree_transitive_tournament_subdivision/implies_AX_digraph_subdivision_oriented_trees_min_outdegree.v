(** * Subdivisions of transitive tournaments imply subdivisions of oriented trees

An oriented tree F is acyclic, hence has a topological order, which embeds it in the transitive
tournament on #|F| vertices.  A subdivision of this tournament contains a subdivision of each of
its subdigraphs: keep the branch vertices and the paths of the arcs of F.  So the bound given for
the transitive tournament of order #|F| works for F.

The implication is the edge e074 of relations.json in graph-conjectures.  It was formalized in
graph-theory-rocq (digraph-theory/theories/conjectures/implications_X2.v). *)

From GraphTheory Require Import digraph.
From mathcomp Require Import boot.
From GC.GraphLib Require Import digraph.
From GC.digraph.OPG_outdegree_transitive_tournament_subdivision Require Import
  main(OPG_outdegree_transitive_tournament_subdivision).
From GC.digraph.AX_digraph_subdivision_oriented_trees_min_outdegree Require Import
  main(AX_digraph_subdivision_oriented_trees_min_outdegree).

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Theorem OPG_outdegree_transitive_tournament_subdivision_implies_AX_digraph_subdivision_oriented_trees_min_outdegree :
  OPG_outdegree_transitive_tournament_subdivision ->
  AX_digraph_subdivision_oriented_trees_min_outdegree.
Proof.
move=> TT F [_ or [forest _]]; have [m Hm] := TT #|F|; exists m => D D0 deg.
apply: disubdivision_subdigraph (Hm D D0 deg).
exact/acyclic_subdigraph_transitive_tournament/oriented_forest_acyclic.
Qed.

Check (OPG_outdegree_transitive_tournament_subdivision_implies_AX_digraph_subdivision_oriented_trees_min_outdegree :
  GC.digraph.OPG_outdegree_transitive_tournament_subdivision.main.OPG_outdegree_transitive_tournament_subdivision ->
  GC.digraph.AX_digraph_subdivision_oriented_trees_min_outdegree.main.AX_digraph_subdivision_oriented_trees_min_outdegree).
Print Assumptions OPG_outdegree_transitive_tournament_subdivision_implies_AX_digraph_subdivision_oriented_trees_min_outdegree.
