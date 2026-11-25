From GC.misc.AX_long_odd_hole_heavy_path_lemma Require Import main(AX_long_odd_hole_heavy_path_lemma).
From GC.misc.AX_long_odd_hole_heavy_path_lemma Require counterexample.

Theorem AX_long_odd_hole_heavy_path_lemma_fails : ~ AX_long_odd_hole_heavy_path_lemma.
Proof. exact counterexample.disproof. Qed.

Check (AX_long_odd_hole_heavy_path_lemma_fails :
  ~ GC.misc.AX_long_odd_hole_heavy_path_lemma.main.AX_long_odd_hole_heavy_path_lemma).
Print Assumptions AX_long_odd_hole_heavy_path_lemma_fails.
