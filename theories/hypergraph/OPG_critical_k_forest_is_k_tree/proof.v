From GC.hypergraph.OPG_critical_k_forest_is_k_tree Require Import main(OPG_critical_k_forest_is_k_tree).
From GC.hypergraph.OPG_critical_k_forest_is_k_tree Require counterexample.

Theorem OPG_critical_k_forest_is_k_tree_fails : ~ OPG_critical_k_forest_is_k_tree.
Proof. exact counterexample.disproof. Qed.

Check (OPG_critical_k_forest_is_k_tree_fails :
  ~ GC.hypergraph.OPG_critical_k_forest_is_k_tree.main.OPG_critical_k_forest_is_k_tree).
Print Assumptions OPG_critical_k_forest_is_k_tree_fails.
