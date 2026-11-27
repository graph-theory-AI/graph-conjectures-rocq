(** * The Matthews-Sumner conjecture implies Thomassen's conjecture on line graphs

Line graphs are claw-free, so a 4-connected line graph is a 4-connected claw-free graph, which is
Hamiltonian by the Matthews-Sumner conjecture.  The converse also holds, by Ryjáček's closure
(J. Combin. Theory Ser. B 70 (1997)), and is not proved here.

The equivalence is the edge e234 of relations.json in graph-conjectures.  This direction was
formalized in graph-theory-rocq (hamiltonicity-theory/theories/conjectures/implications_X211.v). *)

From GraphTheory Require Import digraph sgraph.
From mathcomp Require Import boot.
From GC.GraphLib Require Import hamiltonicity.
From GC.hamiltonicity.BM_matthews_sumner_4_connected_claw_free_hamiltonian Require Import
  main(BM_matthews_sumner_4_connected_claw_free_hamiltonian).
From GC.hamiltonicity.OPG_thomassen_4_connected_line_graphs_hamiltonian Require Import
  main(OPG_thomassen_4_connected_line_graphs_hamiltonian).

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Theorem BM_matthews_sumner_4_connected_claw_free_hamiltonian_implies_OPG_thomassen_4_connected_line_graphs_hamiltonian :
  BM_matthews_sumner_4_connected_claw_free_hamiltonian ->
  OPG_thomassen_4_connected_line_graphs_hamiltonian.
Proof. by move=> MS G conn; apply: MS conn _; apply: simple_line_graph_claw_free. Qed.

Check (BM_matthews_sumner_4_connected_claw_free_hamiltonian_implies_OPG_thomassen_4_connected_line_graphs_hamiltonian :
  GC.hamiltonicity.BM_matthews_sumner_4_connected_claw_free_hamiltonian.main.BM_matthews_sumner_4_connected_claw_free_hamiltonian ->
  GC.hamiltonicity.OPG_thomassen_4_connected_line_graphs_hamiltonian.main.OPG_thomassen_4_connected_line_graphs_hamiltonian).
Print Assumptions BM_matthews_sumner_4_connected_claw_free_hamiltonian_implies_OPG_thomassen_4_connected_line_graphs_hamiltonian.
