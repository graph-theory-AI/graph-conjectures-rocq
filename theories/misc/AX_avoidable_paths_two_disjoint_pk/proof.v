From GC.misc.AX_avoidable_paths_two_disjoint_pk Require Import main(AX_avoidable_paths_two_disjoint_pk).
From GC.misc.AX_avoidable_paths_two_disjoint_pk Require counterexample.

Theorem AX_avoidable_paths_two_disjoint_pk_fails : ~ AX_avoidable_paths_two_disjoint_pk.
Proof. exact counterexample.disproof. Qed.

Check (AX_avoidable_paths_two_disjoint_pk_fails :
  ~ GC.misc.AX_avoidable_paths_two_disjoint_pk.main.AX_avoidable_paths_two_disjoint_pk).
Print Assumptions AX_avoidable_paths_two_disjoint_pk_fails.
