From GC.extremal.AX_bipartite_concatenation_psi_symmetry Require Import main(AX_bipartite_concatenation_psi_symmetry).
From GC.extremal.AX_bipartite_concatenation_psi_symmetry Require asymmetry.

Theorem AX_bipartite_concatenation_psi_symmetry_fails :
  ~ AX_bipartite_concatenation_psi_symmetry.
Proof. exact asymmetry.psi_asymmetry. Qed.

Check (AX_bipartite_concatenation_psi_symmetry_fails :
  ~ GC.extremal.AX_bipartite_concatenation_psi_symmetry.main.AX_bipartite_concatenation_psi_symmetry).
Print Assumptions AX_bipartite_concatenation_psi_symmetry_fails.
