(** * The Berge-Fulkerson conjecture implies the conjecture on the intersection of two perfect
    matchings

A perfect matching [M] of a loopless cubic graph meets every odd cut ([pm_meets_odd_cut]): the
sum of the degrees in [M] of the vertices of a set [S] is [#|S|], and has the parity of the number
of edges of [M] in the cut of [S] ([odd_mdeg_sum]); similarly, [3 #|S|] has the parity of the
size of the cut.  Let [M1], ..., [M6] be perfect matchings covering every edge exactly twice.  An
odd cut contained in [M1 ∩ M2] would meet [M3], and an edge in [M1], [M2] and [M3] would be
covered three times.

The implication is the edge e092 of relations.json in graph-conjectures.  It was formalized in
graph-theory-rocq (cycle-theory/theories/conjectures/implications_U10.v). *)

From GraphTheory Require Import mgraph.
From mathcomp Require Import boot.
From GC.GraphLib Require Import misc cycle packing even_subgraph.
From GC.cycle.OPG_berge_fulkerson_cubic_6_perfect_matchings Require Import
  main(OPG_berge_fulkerson_cubic_6_perfect_matchings).
From GC.cycle.OPG_cubic_two_perfect_matchings_odd_cut Require Import
  main(OPG_cubic_two_perfect_matchings_odd_cut).

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** A perfect matching of a loopless cubic graph meets every odd cut. *)
Lemma pm_meets_odd_cut (G : mgraph) (M : {set edge G}) (S : {set G}) :
  loopless_cubic G -> mperfect_matching M -> odd #|mcut S| -> exists e, e \in M :&: mcut S.
Proof.
case=> ll cub pm oS; apply/set0Pn; rewrite -card_gt0; apply: odd_gt0.
rewrite -odd_mdeg_sum (eq_bigr _ (fun v _ => pm v)) sum1_card.
move: oS; rewrite -(setTI (mcut S)) -odd_mdeg_sum.
have d3 v : mdeg_in [set: edge G] v = 3 by rewrite mdeg_in_loopless // setTI cub.
by rewrite (eq_bigr _ (fun v _ => d3 v)) sum_nat_const oddM andbT.
Qed.

Theorem
  OPG_berge_fulkerson_cubic_6_perfect_matchings_implies_OPG_cubic_two_perfect_matchings_odd_cut :
  OPG_berge_fulkerson_cubic_6_perfect_matchings -> OPG_cubic_two_perfect_matchings_odd_cut.
Proof.
move=> bf G G0 [Gc bl]; have [L [sL pm cov]] := bf G G0 (conj Gc bl).
move: L sL pm cov => [|M1 [|M2 [|M3 L]]] // _ pm cov.
exists M1, M2; split; [by apply: pm; rewrite !inE eqxx | by apply: pm; rewrite !inE eqxx orbT|].
case=> T [/subsetP sub [S [TS _]]]; rewrite TS in sub * => oS.
have [|e /setIP[e3 eS]] := pm_meets_odd_cut Gc (pm M3 _) oS; first by rewrite !inE eqxx !orbT.
by move: (cov e) (sub e eS); rewrite /= inE e3 => + /andP[e1 e2]; rewrite e1 e2.
Qed.

Check (
  OPG_berge_fulkerson_cubic_6_perfect_matchings_implies_OPG_cubic_two_perfect_matchings_odd_cut :
  GC.cycle.OPG_berge_fulkerson_cubic_6_perfect_matchings.main.OPG_berge_fulkerson_cubic_6_perfect_matchings ->
  GC.cycle.OPG_cubic_two_perfect_matchings_odd_cut.main.OPG_cubic_two_perfect_matchings_odd_cut).

Print Assumptions
  OPG_berge_fulkerson_cubic_6_perfect_matchings_implies_OPG_cubic_two_perfect_matchings_odd_cut.
