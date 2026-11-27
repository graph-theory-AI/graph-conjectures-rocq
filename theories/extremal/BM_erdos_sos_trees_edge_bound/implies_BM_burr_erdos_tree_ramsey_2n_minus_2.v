(** * The Erdős-Sós conjecture implies the Burr-Erdős bound on the Ramsey number of trees

Let T be a tree with n >= 2 vertices, hence k = n - 1 >= 1 edges, and colour the edges of K_2k
with two colours.  One colour class has at least half of the k (2k - 1) edges, more than the
Erdős-Sós threshold 2k (k - 1) / 2, so it contains T.

The implication is the edge e239 of relations.json in graph-conjectures.  It was formalized in
graph-theory-rocq (extremal-graph-theory/theories/conjectures/implications_X215.v). *)

From GraphTheory Require Import digraph sgraph.
From mathcomp Require Import boot zify_ssreflect.
From GC.GraphLib Require Import chromatic extremal.
From GC.extremal.BM_erdos_sos_trees_edge_bound Require Import main(BM_erdos_sos_trees_edge_bound).
From GC.extremal.BM_burr_erdos_tree_ramsey_2n_minus_2 Require Import
  main(BM_burr_erdos_tree_ramsey_2n_minus_2).

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Theorem BM_erdos_sos_trees_edge_bound_implies_BM_burr_erdos_tree_ramsey_2n_minus_2 :
  BM_erdos_sos_trees_edge_bound -> BM_burr_erdos_tree_ramsey_2n_minus_2.
Proof.
move=> ES T treeT T1; case/card_gt0P: (ltnW T1) => r _.
rewrite -(tree_card_edges treeT r) in T1 *; rewrite mulnS addKn; set k := #|E(T)| => col.
pose class c := edge_color_class col (pred1 c).
have split : #|E('K_(2 * k))| = #|E(class ord0)| + #|E(class ord_max)|.
  rewrite !edge_color_class_edges -(cardsID [set e | col e == ord0]); congr (_ + _).
    by apply: eq_card => e; rewrite !inE.
  by apply: eq_card => e; rewrite !inE andbC; case: (col e) => -[|[|]].
have [c Hc] : exists c, #|E('K_(2 * k))| <= 2 * #|E(class c)|.
  by case: (leqP #|E(class ord_max)| #|E(class ord0)|) => h;
    [exists ord0 | exists ord_max]; rewrite split mul2n -addnn ?leq_add2l ?leq_add2r // ltnW.
exists ord0, c; apply: (ES _ T k treeT erefl); rewrite card_ord.
have bin : 'C(2 * k, 2) = k * (2 * k).-1 by rewrite bin2 mul2n -doubleMl doubleK.
by move: Hc T1; rewrite card_edge_Kn bin; set m := #|E(_)|; lia.
Qed.

Check (BM_erdos_sos_trees_edge_bound_implies_BM_burr_erdos_tree_ramsey_2n_minus_2 :
  GC.extremal.BM_erdos_sos_trees_edge_bound.main.BM_erdos_sos_trees_edge_bound ->
  GC.extremal.BM_burr_erdos_tree_ramsey_2n_minus_2.main.BM_burr_erdos_tree_ramsey_2n_minus_2).
Print Assumptions BM_erdos_sos_trees_edge_bound_implies_BM_burr_erdos_tree_ramsey_2n_minus_2.
