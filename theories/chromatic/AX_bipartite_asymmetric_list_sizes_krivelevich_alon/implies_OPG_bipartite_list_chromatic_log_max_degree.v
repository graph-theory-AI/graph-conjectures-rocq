(** * Asymmetric list sizes in bipartite graphs imply that the choice number is O(log Δ)

Let G be a bipartite graph of maximum degree Δ >= 2, with parts A and B.  Case (ii) of the
conjecture of Alon, Cambie and Kang, with Δ_A = Δ_B = Δ and k_A = k_B = C log Δ, says that G is
(C log Δ)-choosable.  Hence its choice number m satisfies m <= C log Δ, that is 2^m <= Δ^C.

The implication is the edge e025 of relations.json in graph-conjectures.  It was formalized in
graph-theory-rocq (atlas/theories/conjectures/implications_A1.v). *)

From GraphTheory Require Import digraph sgraph connectivity.
From mathcomp Require Import boot.
From GC.chromatic.AX_bipartite_asymmetric_list_sizes_krivelevich_alon Require Import
  main(AX_bipartite_asymmetric_list_sizes_krivelevich_alon).
From GC.extremal.OPG_bipartite_list_chromatic_log_max_degree Require Import
  main(OPG_bipartite_list_chromatic_log_max_degree).

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Abbreviation Delta := GC.extremal.OPG_bipartite_list_chromatic_log_max_degree.main.Delta.

Theorem AX_bipartite_asymmetric_list_sizes_krivelevich_alon_implies_OPG_bipartite_list_chromatic_log_max_degree :
  AX_bipartite_asymmetric_list_sizes_krivelevich_alon ->
  OPG_bipartite_list_chromatic_log_max_degree.
Proof.
case=> _ [[C C1 HC] _]; exists C => G m [A bipA] D2 [_ minm].
pose k := C * trunc_log 2 (Delta G).
have degD (S : {set G}) v : v \in S -> #|N(v)| <= Delta G by move=> _; exact: leq_bigmax.
have k0 : 0 < k by rewrite muln_gt0 trunc_log_gt0 D2 ltnW.
have mk : m <= k.
  by apply: minm => P L HL; apply: (HC G A _ _ k k bipA (degD _) (degD _)) => // v _.
apply: leq_trans (_ : 2 ^ k <= _); first by rewrite leq_pexp2l.
by rewrite /k mulnC expnM leq_exp2r ?trunc_logP // ltnW.
Qed.

Check (AX_bipartite_asymmetric_list_sizes_krivelevich_alon_implies_OPG_bipartite_list_chromatic_log_max_degree :
  GC.chromatic.AX_bipartite_asymmetric_list_sizes_krivelevich_alon.main.AX_bipartite_asymmetric_list_sizes_krivelevich_alon ->
  GC.extremal.OPG_bipartite_list_chromatic_log_max_degree.main.OPG_bipartite_list_chromatic_log_max_degree).
Print Assumptions AX_bipartite_asymmetric_list_sizes_krivelevich_alon_implies_OPG_bipartite_list_chromatic_log_max_degree.
