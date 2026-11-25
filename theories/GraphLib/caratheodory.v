(** * Carathéodory's theorem

    A convex combination of points of a space of dimension d is a convex combination of at most d+1
    of these points (C. Carathéodory, 1911) [caratheodory].

    If more than d+1 coefficients are nonzero, then the corresponding points are affinely dependent
    [dependency].  A multiple of the dependency is subtracted from the coefficients, such that they
    remain nonnegative and one more coefficient vanishes. *)

From mathcomp Require Import boot order algebra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Num.Theory Order.POrderTheory Order.TotalTheory.
Local Open Scope ring_scope.

Section Caratheodory.
Variables (R : realFieldType) (d : nat) (T : finType) (z : T -> 'rV[R]_d).

(** More than [d.+1] points are affinely dependent. *)
Lemma dependency (S : {set T}) : (d.+1 < #|S|)%N -> exists nu : T -> R,
  [/\ forall t, t \notin S -> nu t = 0, exists t, nu t != 0,
      \sum_t nu t = 0 & \sum_t nu t *: z t = 0].
Proof.
move=> S_gt; pose A := \matrix_(i < #|S|) row_mx (1 : 'M[R]_1) (z (enum_val i)).
have [u /sub_kermxP uA u0] : exists2 u : 'rV_#|S|, (u <= kermx A)%MS & u != 0.
  by apply/rowV0Pn; rewrite kermx_eq0 -row_leq_rank -ltnNge (leq_ltn_trans (rank_leq_col A)).
have sum_val (V : lmodType R) (v : T -> V) :
    \sum_t (\sum_(i | enum_val i == t) u 0 i) *: v t = \sum_i u 0 i *: v (enum_val i).
  rewrite [RHS](partition_big enum_val xpredT) //=; apply: eq_bigr => t _.
  by rewrite scaler_suml; apply: eq_bigr => i /eqP->.
have : \sum_i u 0 i *: row_mx (1 : 'M[R]_1) (z (enum_val i)) = 0.
  by rewrite -[RHS]uA mulmx_sum_row; apply: eq_bigr => i _; rewrite rowK.
rewrite -(sum_val _ (fun t => row_mx 1 (z t))) => dep.
exists (fun t => \sum_(i | enum_val i == t) u 0 i); split.
- move=> t tS; rewrite big_pred0 // => i; apply: contraNF tS => /eqP<-.
  exact: enum_valP.
- have /rV0Pn[i ui] := u0; exists (enum_val i).
  by rewrite (big_pred1 i) // => j; rewrite (inj_eq enum_val_inj).
- have := congr1 lsubmx dep; rewrite linear0 linear_sum /=.
  under eq_bigr do rewrite linearZ /= row_mxKl.
  by rewrite -scaler_suml => /eqP; rewrite scaler_eq0 oner_eq0 orbF => /eqP.
have := congr1 rsubmx dep; rewrite linear0 linear_sum /=.
by under eq_bigr do rewrite linearZ /= row_mxKr.
Qed.

Theorem caratheodory (lam : T -> R) : (forall t, 0 <= lam t) -> \sum_t lam t = 1 ->
  exists mu : T -> R,
    [/\ forall t, 0 <= mu t, \sum_t mu t = 1, \sum_t mu t *: z t = \sum_t lam t *: z t
      & (#|[set t | mu t != 0%R]| <= d.+1)%N].
Proof.
have [n] := ubnP #|[set t | lam t != 0]|; elim: n lam => // n IH lam /ltnSE le_n lam0 lam1.
have [?|/dependency[nu [nuS [t1 nu1] sum_nu dep]]] := leqP #|[set t | lam t != 0]| d.+1.
  by exists lam.
have /existsP[t2 nu2] : [exists t, 0 < nu t].
  apply: contraNT nu1 => /existsPn no; have nonpos t : 0 <= - nu t by rewrite oppr_ge0 leNgt no.
  have := psumr_eq0P (P := predT) (fun t _ => nonpos t); rewrite sumrN sum_nu oppr0.
  by move=> /(_ erefl t1 isT)/eqP; rewrite oppr_eq0.
have [m nu_m min_m] := @arg_minP _ _ _ t2 (fun t => 0 < nu t) (fun t => lam t / nu t) nu2.
pose th := lam m / nu m; pose mu t := lam t - th * nu t.
have mu_m : mu m = 0 by rewrite /mu divfK ?subrr ?gt_eqF.
have lam_m : lam m != 0 by apply: contraTneq nu_m => e; rewrite nuS ?ltxx // inE e eqxx.
have [|t||kap [kap0 kap1 kap_z kap_card]] := IH mu.
- apply: leq_trans le_n; apply/proper_card/properP; split; last first.
    by exists m; rewrite !inE ?mu_m ?eqxx.
  apply/subsetP => t; rewrite !inE; apply: contraNneq => e.
  by rewrite /mu e nuS ?mulr0 ?subrr // inE e eqxx.
- rewrite subr_ge0; have [nu_t|nu_t] := lerP (nu t) 0; last by rewrite -ler_pdivlMr ?min_m.
  by rewrite (le_trans _ (lam0 t)) // mulr_ge0_le0 // divr_ge0 // ltW.
- by rewrite sumrB -mulr_sumr sum_nu mulr0 subr0.
exists kap; split=> //; rewrite kap_z; under eq_bigr do rewrite scalerBl -scalerA.
by rewrite sumrB -scaler_sumr dep scaler0 subr0.
Qed.

End Caratheodory.
