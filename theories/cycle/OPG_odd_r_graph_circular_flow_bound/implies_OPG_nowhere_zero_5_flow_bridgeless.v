(** * The circular flow conjecture for odd r-graphs implies the 5-flow conjecture

The case [t = 4] of the conjecture says that every 9-graph has circular flow number at most 5/2.
Let [G] be bridgeless.  Its inflation [H] (every vertex replaced by a cycle through its ends) is
loopless and cubic, and its odd cuts have at least 3 edges: a cut splitting a cycle has at least
2 edges, the cut of a union of cycles is a cut of [G], and in a cubic graph the cut of an odd set
of vertices has an odd number of edges.
Hence [3H], with every edge tripled, is a 9-graph.  Twice a circular [(5 + eps)/2]-flow of [3H],
for [eps < 1/m] with [m] edges, has absolute values between 2 and [3 + eps], so it rounds to an
integer flow with values ±2 and ±3 ([rat_flow_round_abs], the argument of Goddyn, Tarsi and
Zhang).  The sums over the three copies of each edge are never multiples of 5; on the copies of
the edges of [G] they form a nowhere-zero Z_5-flow of [G], which Tutte's theorem turns into a
nowhere-zero 5-flow ([mod_flow_nowhere_zero]).

The implication is the edge e185 of relations.json in graph-conjectures.  It was formalized in
graph-theory-rocq (cycle-theory/theories/conjectures/implications_D1.v). *)

From GraphTheory Require Import mgraph.
From mathcomp Require Import boot order algebra.
From GC.GraphLib Require Import misc chromatic cycle cubic_inflation flow.
From GC.cycle.OPG_odd_r_graph_circular_flow_bound Require Import inflation_mult.
From GC.cycle.OPG_odd_r_graph_circular_flow_bound Require Import
  main(OPG_odd_r_graph_circular_flow_bound).
From GC.cycle.OPG_nowhere_zero_5_flow_bridgeless Require Import
  main(OPG_nowhere_zero_5_flow_bridgeless).

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Num.Theory Order.TTheory.

(** A sum of three integers of absolute value 2 or 3 is not a multiple of 5. *)
Lemma sum3_mod5 (x y z : int) :
  (2 <= `|x| <= 3 -> 2 <= `|y| <= 3 -> 2 <= `|z| <= 3 -> ~~ (5 %| x + y + z)%Z)%R.
Proof.
have mem (u : int) : (2 <= `|u| <= 3)%R -> u \in [:: 2; -2; 3; -3]%R.
  by case: u => [[|[|[|[|]]]]|[|[|[|]]]].
by move=> /mem + /mem + /mem; rewrite !inE => /or4P[]/eqP-> /or4P[]/eqP-> /or4P[]/eqP->.
Qed.

Theorem OPG_odd_r_graph_circular_flow_bound_implies_OPG_nowhere_zero_5_flow_bridgeless :
  OPG_odd_r_graph_circular_flow_bound -> OPG_nowhere_zero_5_flow_bridgeless.
Proof.
move=> HA G E0 hbl.
have no1 (S : {set G}) : #|mcut S| != 1.
  apply/eqP => c1; have /set0Pn[e eS] : mcut S != set0 by rewrite -card_gt0 c1.
  by have := bridgeless_mcut hbl eS; rewrite c1.
have nn := nxt_neq hbl; pose H := infl G 1; pose H3 := medge_mult H 3.
have ll : mloopless H := infl_loopless nn; have reg : mregular H 3 := infl_regular nn.
have cut3 (X : {set H}) : odd #|X| -> 3 <= #|mcut X|.
  move=> oddX; have : odd #|mcut X| by rewrite (mregular_mcut_odd _ ll reg) oddM oddX.
  case: (infl_mcut X) => [|[S XS]]; first by case: #|mcut X| => [|[|[|]]].
  by move: (no1 S); rewrite XS infl_mcut_union; case: #|mcut S| => [|[|[|]]].
have rH3 : r_graph H3 (2 * 4 + 1).
  split=> [v|X oddX]; first by rewrite medge_mult_edges_at reg.
  by rewrite medge_mult_mcut (@leq_trans (3 * 3)) // leq_mul2r cut3.
have H30 : 0 < #|H3| by have := infl_card G 1; rewrite /H3 /= => ->; rewrite muln_gt0.
pose eps : rat := (#|edge H3|.+1%:R)^-1.
have eps0 : (0 < eps)%R by rewrite invr_gt0 ltr0n.
have [phi [cphi bphi]] : circular_flow H3 ((5%:R + eps) / 2%:R)%R.
  apply: (HA 4 H3 isT H30 rH3).
  have -> : (2 + 2 / 4 = 5 / 2 :> rat)%R by apply/eqP; vm_compute.
  by rewrite ltr_pM2r ?invr_gt0 ?ltr0n // ltrDl.
pose psi e := (2%:R * phi e)%R.
have cpsi : conservative psi.
  by apply/conservativeE => v; rewrite mnetZ; move/conservativeE: cphi => ->; rewrite mulr0.
have [||g [cg bg]] := @rat_flow_round_abs _ psi 2 eps cpsi (ltW eps0).
- by rewrite ltr_pdivrMr ?ltr0n // mul1r ltr_nat.
- move=> e; have [lo hi] := bphi e; rewrite /psi normrM normr_nat.
  apply/andP; split; first by rewrite -[X in (X <= _)%R]mulr1 ler_pM2l.
  apply: (@le_trans _ _ (2 * ((5 + eps) / 2 - 1))%R); first by rewrite ler_pM2l.
  by rewrite mulrBr mulr1 mulrC divfK // lerBlDr addrAC lerD2r.
pose f e := (\sum_(i < 3) g (e, i))%R.
have cf : conservative f.
  by apply/conservativeE => v; rewrite (medge_mult_mnet g); move/conservativeE: cg.
apply: (@mod_flow_nowhere_zero _ 5 (fun e => f (inl e))) => // [v|e].
  by move/conservativeE: (infl_contract cf) => ->.
by rewrite /f !big_ord_recl big_ord0 addr0 addrA; apply: sum3_mod5; apply: bg.
Qed.

Check (OPG_odd_r_graph_circular_flow_bound_implies_OPG_nowhere_zero_5_flow_bridgeless :
  GC.cycle.OPG_odd_r_graph_circular_flow_bound.main.OPG_odd_r_graph_circular_flow_bound ->
  GC.cycle.OPG_nowhere_zero_5_flow_bridgeless.main.OPG_nowhere_zero_5_flow_bridgeless).
Print Assumptions OPG_odd_r_graph_circular_flow_bound_implies_OPG_nowhere_zero_5_flow_bridgeless.
