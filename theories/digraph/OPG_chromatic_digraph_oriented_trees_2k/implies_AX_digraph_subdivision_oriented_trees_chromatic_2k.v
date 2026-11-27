(** * Burr's conjecture implies the chromatic Mader bound for oriented trees

Let T be an oriented tree of order k and D a non-empty digraph with χ(D) >= 2k-2.  If k >= 2,
Burr's conjecture gives a copy of T in D, and a copy of a loopless digraph is a subdivision of it,
each arc being replaced by the path of length one.  If k <= 1, T has at most one vertex and no
arc: any vertex of D is a copy of T.

The implication is the edge e019 of relations.json in graph-conjectures.  It was formalized in
graph-theory-rocq (digraph-theory/theories/conjectures/implications_X52.v). *)

From GraphTheory Require Import digraph.
From mathcomp Require Import boot.
From GC.GraphLib Require Import digraph.
From GC.digraph.OPG_chromatic_digraph_oriented_trees_2k Require Import
  main(OPG_chromatic_digraph_oriented_trees_2k).
From GC.digraph.AX_digraph_subdivision_oriented_trees_chromatic_2k Require Import
  main(AX_digraph_subdivision_oriented_trees_chromatic_2k).

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Theorem OPG_chromatic_digraph_oriented_trees_2k_implies_AX_digraph_subdivision_oriented_trees_chromatic_2k :
  OPG_chromatic_digraph_oriented_trees_2k -> AX_digraph_subdivision_oriented_trees_chromatic_2k.
Proof.
move=> burr T k Tt Tk D D0 chi; have [_ Tor _] := Tt.
have irr : irreflexive (@edge_rel T).
  by move=> x; apply/negP => xx; have := Tor x x xx; rewrite xx.
apply: subdigraph_disubdivision => //.
have [k2|k1] := ltnP 1 k; first exact: burr _ _ k2 chi _ Tt Tk.
have [x0 _] := card_gt0P D0; rewrite -Tk in k1; move/fintype_le1P: k1 => T1.
by exists (fun _ => x0); split=> [u v _|u v]; rewrite ?(T1 u v) ?irr.
Qed.

Check (OPG_chromatic_digraph_oriented_trees_2k_implies_AX_digraph_subdivision_oriented_trees_chromatic_2k :
  GC.digraph.OPG_chromatic_digraph_oriented_trees_2k.main.OPG_chromatic_digraph_oriented_trees_2k ->
  GC.digraph.AX_digraph_subdivision_oriented_trees_chromatic_2k.main.AX_digraph_subdivision_oriented_trees_chromatic_2k).
Print Assumptions OPG_chromatic_digraph_oriented_trees_2k_implies_AX_digraph_subdivision_oriented_trees_chromatic_2k.
