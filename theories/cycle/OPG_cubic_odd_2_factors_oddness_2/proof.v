From GC.cycle.OPG_cubic_odd_2_factors_oddness_2 Require Import main(OPG_cubic_odd_2_factors_oddness_2).
From GC.cycle.OPG_cubic_odd_2_factors_oddness_2 Require counterexample.

Theorem OPG_cubic_odd_2_factors_oddness_2_fails : ~ OPG_cubic_odd_2_factors_oddness_2.
Proof. exact counterexample.disproof. Qed.

Check (OPG_cubic_odd_2_factors_oddness_2_fails : ~ GC.cycle.OPG_cubic_odd_2_factors_oddness_2.main.OPG_cubic_odd_2_factors_oddness_2).
Print Assumptions OPG_cubic_odd_2_factors_oddness_2_fails.
