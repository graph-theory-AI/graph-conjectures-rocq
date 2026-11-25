From GC.packing.OPG_matching_cut_average_degree_girth Require Import main(OPG_matching_cut_average_degree_girth).
From GC.packing.OPG_matching_cut_average_degree_girth Require counterexample.

Theorem OPG_matching_cut_average_degree_girth_fails :
  ~ OPG_matching_cut_average_degree_girth.
Proof. exact counterexample.counterexample. Qed.

Check (OPG_matching_cut_average_degree_girth_fails :
  ~ GC.packing.OPG_matching_cut_average_degree_girth.main.OPG_matching_cut_average_degree_girth).
Print Assumptions OPG_matching_cut_average_degree_girth_fails.
