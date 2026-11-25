From GC.misc.AX_planar_fvs_face_packing_ratio_2 Require Import main(AX_planar_fvs_face_packing_ratio_2).
From GC.misc.AX_planar_fvs_face_packing_ratio_2 Require disproof.

Theorem AX_planar_fvs_face_packing_ratio_2_fails : ~ AX_planar_fvs_face_packing_ratio_2.
Proof. exact disproof.disproof. Qed.

Check (AX_planar_fvs_face_packing_ratio_2_fails :
  ~ GC.misc.AX_planar_fvs_face_packing_ratio_2.main.AX_planar_fvs_face_packing_ratio_2).
Print Assumptions AX_planar_fvs_face_packing_ratio_2_fails.
