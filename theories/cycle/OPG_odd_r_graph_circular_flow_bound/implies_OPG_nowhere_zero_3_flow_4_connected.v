(** * The circular flow conjecture for odd r-graphs implies the 3-flow conjecture

The case [t = 2] of the conjecture says that every 5-graph has circular flow number at most 3.
Let [G] be 4-edge-connected.  Its inflation [H] (every vertex replaced by a cycle through its
ends, whose edges are doubled) is a 5-graph: it is loopless and 5-regular, a cut splitting a
cycle has at least 4 edges, the cut of a union of cycles is a cut of [G], and in a 5-regular
graph the cut of an odd set of vertices has an odd number of edges.  A circular
[(3 + eps)]-flow of [H], for [eps < 1/m] with [m] edges, has absolute values between 1 and
[2 + eps], so it rounds to an integer flow with absolute values 1 and 2 ([rat_flow_round_abs],
the argument of Goddyn, Tarsi and Zhang), which contracts to a nowhere-zero 3-flow of [G].

The implication is the edge e184 of relations.json in graph-conjectures (Steffen, J. Graph
Theory 79 (2015): the case [t = 2] is equivalent to Tutte's 3-flow conjecture).  It was
formalized in graph-theory-rocq (cycle-theory/theories/conjectures/implications_D1.v). *)

From GraphTheory Require Import mgraph.
From mathcomp Require Import boot order algebra.
From GC.GraphLib Require Import misc chromatic cycle flow.
From GC.cycle.OPG_odd_r_graph_circular_flow_bound Require Import inflation_mult.
From GC.cycle.OPG_odd_r_graph_circular_flow_bound Require Import
  main(OPG_odd_r_graph_circular_flow_bound).
From GC.cycle.OPG_nowhere_zero_3_flow_4_connected Require Import
  main(OPG_nowhere_zero_3_flow_4_connected).

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Num.Theory Order.TTheory.

Theorem OPG_odd_r_graph_circular_flow_bound_implies_OPG_nowhere_zero_3_flow_4_connected :
  OPG_odd_r_graph_circular_flow_bound -> OPG_nowhere_zero_3_flow_4_connected.
Proof.
move=> HA G E0 G4; have cut4 := medge_connected_mcut G4.
have no1 (S : {set G}) : #|mcut S| != 1.
  apply/eqP => c1; have /set0Pn[e] : mcut S != set0 by rewrite -card_gt0 c1.
  rewrite inE; case sS: (source e \in S) => /= tS.
    by have := cut4 S _ _ sS tS; rewrite c1.
  by have := cut4 S _ _ tS (negbT sS); rewrite c1.
have nn := infl_nxt_neq no1; pose H := infl G 2.
have H0 : 0 < #|H| by rewrite infl_card muln_gt0.
have rH : r_graph H (2 * 2 + 1).
  split=> [|X oddX]; first exact: infl_regular nn.
  have : odd #|mcut X|.
    by rewrite (mregular_mcut_odd _ (infl_loopless nn) (infl_regular nn)) oddM oddX.
  suff : 4 <= #|mcut X| by rewrite leq_eqVlt => /orP[/eqP <-|].
  case: (infl_mcut X) => [//|[S XS]]; rewrite XS infl_mcut_union.
  by rewrite XS in oddX; have [x [y [xS yS]]] := infl_union_odd oddX; apply: cut4 xS yS.
pose eps : rat := (#|edge H|.+1%:R)^-1.
have eps0 : (0 < eps)%R by rewrite invr_gt0 ltr0n.
have [phi [cphi bphi]] : circular_flow H (3%:R + eps)%R.
  by apply: (HA 2 H isT H0 rH); rewrite divff // (_ : 2 + 1 = 3)%R // ltrDl.
have [||g [cg bg]] := @rat_flow_round_abs _ phi 1 eps cphi (ltW eps0).
- by rewrite ltr_pdivrMr ?ltr0n // mul1r ltr_nat.
- move=> e; have [lo hi] := bphi e; apply/andP; split => //.
  by rewrite (le_trans hi) // (_ : 3 = 1 + 1 + 1)%R // addrAC addrK.
exists (fun e => g (inl e)); split; first exact: infl_contract cg.
by move=> e; have /andP[lo hi] := bg (inl e).
Qed.

Check (OPG_odd_r_graph_circular_flow_bound_implies_OPG_nowhere_zero_3_flow_4_connected :
  GC.cycle.OPG_odd_r_graph_circular_flow_bound.main.OPG_odd_r_graph_circular_flow_bound ->
  GC.cycle.OPG_nowhere_zero_3_flow_4_connected.main.OPG_nowhere_zero_3_flow_4_connected).
Print Assumptions OPG_odd_r_graph_circular_flow_bound_implies_OPG_nowhere_zero_3_flow_4_connected.
