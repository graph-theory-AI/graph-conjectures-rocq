(** * Arc-disjoint strong spanning subdigraphs give arc-disjoint out- and in-branchings

Let D be a k-arc-strong digraph, where k is given by the Bang-Jensen-Yeo conjecture, and let A1
and A2 be the arc sets of two arc-disjoint strongly connected spanning subdigraphs.  Every vertex
is reachable from u in A1: the last arc of a shortest walk from u to each vertex x != u gives an
out-branching rooted at u, acyclic because the length of a shortest walk increases along its arcs.
Similarly, shortest walks to v in A2 give an in-branching rooted at v.  They are arc-disjoint since
A1 and A2 are.

The implication is the edge e103 of relations.json in graph-conjectures.  It was formalized in
graph-theory-rocq (digraph-theory/theories/conjectures/implications_P9.v). *)

From GraphTheory Require Import digraph.
From mathcomp Require Import boot.
From GC.GraphLib Require Import digraph.
From GC.digraph.OPG_digraph_arc_disjoint_strong_spanning_subdigraphs Require Import
  main(OPG_digraph_arc_disjoint_strong_spanning_subdigraphs).
From GC.digraph.OPG_arc_strong_disjoint_out_in_branchings Require Import
  main(OPG_arc_strong_disjoint_out_in_branchings).

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Theorem OPG_digraph_arc_disjoint_strong_spanning_subdigraphs_implies_OPG_arc_strong_disjoint_out_in_branchings :
  OPG_digraph_arc_disjoint_strong_spanning_subdigraphs ->
  OPG_arc_strong_disjoint_out_in_branchings.
Proof.
move=> [k Hk]; exists k => D u v kD.
have [A1 [A2 [dis s1 s2]]] := Hk D kD.
have [F FA1 oF] := spanning_strong_out_branching u s1.
have [F' FA2 iF'] := spanning_strong_in_branching v s2.
exists F, F'; split=> //.
exact: disjointW FA1 FA2 dis.
Qed.

Check (OPG_digraph_arc_disjoint_strong_spanning_subdigraphs_implies_OPG_arc_strong_disjoint_out_in_branchings :
  GC.digraph.OPG_digraph_arc_disjoint_strong_spanning_subdigraphs.main.OPG_digraph_arc_disjoint_strong_spanning_subdigraphs ->
  GC.digraph.OPG_arc_strong_disjoint_out_in_branchings.main.OPG_arc_strong_disjoint_out_in_branchings).
Print Assumptions OPG_digraph_arc_disjoint_strong_spanning_subdigraphs_implies_OPG_arc_strong_disjoint_out_in_branchings.
