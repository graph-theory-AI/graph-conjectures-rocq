(** * Dense subgraphs of large girth in graphs of large average degree or chromatic number

Thomassen's conjecture (graphs of large average degree have subgraphs of large average degree and
large girth) implies the conjecture of Mohar and Wu (graphs of large chromatic number have
subgraphs of large average degree and large girth).  Let d be given by Thomassen's conjecture for
the girth g and the average degree k.  A graph of chromatic number at least d + 2 has an induced
subgraph of minimum degree at least d + 1 (Szekeres and Wilf), hence of average degree at least d,
which contains a subgraph of average degree at least k and girth greater than g.

The implication is the edge e117 of relations.json in graph-conjectures.  It was formalized in
graph-theory-rocq (atlas/theories/conjectures/implications_A1.v). *)

From GraphTheory Require Import digraph sgraph.
From mathcomp Require Import boot.
From GC.GraphLib Require Import degeneracy.
From GC.misc.OPG_average_degree_subgraph_large_girth Require Import
  main(OPG_average_degree_subgraph_large_girth).
From GC.chromatic.AX_large_chromatic_high_girth_dense_subgraph Require Import
  main(AX_large_chromatic_high_girth_dense_subgraph).

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Theorem OPG_average_degree_subgraph_large_girth_implies_AX_large_chromatic_high_girth_dense_subgraph :
  OPG_average_degree_subgraph_large_girth -> AX_large_chromatic_high_girth_dense_subgraph.
Proof.
move=> thomassen k g k0 g3; have [d dP] := thomassen g k (ltnW (ltnW g3)) k0.
exists d.+2; split=> // G chiG.
have [S [S0 degS]] := chi_min_degree_subgraph (k := d.+1) isT chiG.
have [||H [H0 [f finj fhom] avH girH]] := dP (induced S).
- by have [v vS] := set0Pn _ S0; apply/card_gt0P; exists (Sub v vS).
- red; rewrite mul1n mulnC -sum_nat_const.
  by apply: leq_sum => x _; exact: ltnW.
exists H; split=> // [|c cc]; last exact: ltnW (girH c cc).
exists (val \o f) => [|x y xy _]; first exact: inj_comp val_inj finj.
by apply: fhom (xy) _; rewrite (inj_eq finj) (sg_edgeNeq xy).
Qed.

Check (OPG_average_degree_subgraph_large_girth_implies_AX_large_chromatic_high_girth_dense_subgraph :
  GC.misc.OPG_average_degree_subgraph_large_girth.main.OPG_average_degree_subgraph_large_girth ->
  GC.chromatic.AX_large_chromatic_high_girth_dense_subgraph.main.AX_large_chromatic_high_girth_dense_subgraph).
Print Assumptions
  OPG_average_degree_subgraph_large_girth_implies_AX_large_chromatic_high_girth_dense_subgraph.
