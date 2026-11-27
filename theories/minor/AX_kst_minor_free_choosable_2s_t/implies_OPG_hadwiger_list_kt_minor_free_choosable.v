(** * The bound 2s + t for K_{s,t}-minor-free graphs implies the list Hadwiger conjecture

Take the constant c = 3.  Every graph has a K_0 minor, so let t >= 1.  The graph K_t is a minor of
K_{t,t}: contract a perfect matching.  Hence a K_t-minor-free graph has no K_{t,t} minor, and its
choice number is at most 2t + t = 3t.

The implication is the edge e048 of relations.json in graph-conjectures.  It was formalized in
graph-theory-rocq (atlas/theories/conjectures/implications_A1.v). *)

From GraphTheory Require Import digraph sgraph minor.
From mathcomp Require Import boot.
From GC.minor.AX_kst_minor_free_choosable_2s_t Require Import
  main(AX_kst_minor_free_choosable_2s_t).
From GC.chromatic.OPG_hadwiger_list_kt_minor_free_choosable Require Import
  main(OPG_hadwiger_list_kt_minor_free_choosable).

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** [K_n] is a minor of [K_n,n]: the branch set of the vertex [i] is the edge [{inl i, inr i}]. *)
Lemma minor_KB_K (n : nat) : minor 'K_n,n 'K_n.
Proof.
pose phi (i : 'K_n) : {set 'K_n,n} := [set inl i; inr i].
apply: (@minor_of_rmap _ _ phi); split.
- by move=> i; apply/set0Pn; exists (inl i); rewrite !inE eqxx.
- by move=> i; apply: connected2.
- move=> i j ij; rewrite -setI_eq0; apply/eqP/setP => x; rewrite !inE.
  by apply/negbTE/negP => /andP[] /orP[] /eqP-> /orP[] // /eqP[] /eqP; rewrite (negbTE ij).
- by move=> i j _; apply/neighborP; exists (inl i), (inr j); rewrite !inE !eqxx.
Qed.

Theorem AX_kst_minor_free_choosable_2s_t_implies_OPG_hadwiger_list_kt_minor_free_choosable :
  AX_kst_minor_free_choosable_2s_t -> OPG_hadwiger_list_kt_minor_free_choosable.
Proof.
move=> H; exists 3; split=> // G [|t] chG nK hch.
  by case: nK; apply: (@minor_of_clique _ set0) => // x; rewrite inE.
apply: leq_trans (H t.+1 t.+1 chG G isT (leqnn _) _ hch) _; last by rewrite -mulSnr.
by move=> m; apply: nK (minor_trans m (minor_KB_K _)).
Qed.

Check (AX_kst_minor_free_choosable_2s_t_implies_OPG_hadwiger_list_kt_minor_free_choosable :
  GC.minor.AX_kst_minor_free_choosable_2s_t.main.AX_kst_minor_free_choosable_2s_t ->
  GC.chromatic.OPG_hadwiger_list_kt_minor_free_choosable.main.OPG_hadwiger_list_kt_minor_free_choosable).
Print Assumptions AX_kst_minor_free_choosable_2s_t_implies_OPG_hadwiger_list_kt_minor_free_choosable.
