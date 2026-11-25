From GC.digraph.AX_directed_kneser_graphs_existence Require Import main(AX_directed_kneser_graphs_existence).
From GC.digraph.AX_directed_kneser_graphs_existence Require nonexistence.

Theorem AX_directed_kneser_graphs_existence_fails : ~ AX_directed_kneser_graphs_existence.
Proof. exact nonexistence.no_directed_kneser. Qed.

Check (AX_directed_kneser_graphs_existence_fails :
  ~ GC.digraph.AX_directed_kneser_graphs_existence.main.AX_directed_kneser_graphs_existence).
Print Assumptions AX_directed_kneser_graphs_existence_fails.
