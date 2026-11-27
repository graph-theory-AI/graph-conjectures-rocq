(** * The 1/2-flow-pair conjecture implies the 5-flow conjecture

From a 1/2-flow-pair [(phi2, phi4)], the integer flow [chi = 5 phi2 + phi4] has values between 2
and 8 in absolute value: [chi / 2] is a circular nowhere-zero 5-flow.  Tutte's theorem modulo 2
([mod_flow_lift]) gives a flow [h] with values in {-1, 0, 1} and the parity of [chi], and
[(chi + h) / 2] is a nowhere-zero 5-flow.

The implication is the edge e174 of relations.json in graph-conjectures, from the context of
Conjecture 6.1 of arXiv:2511.02892 (with Goddyn, Tarsi and Zhang: the flow number is the ceiling
of the circular flow number).  It was formalized in graph-theory-rocq
(cycle-theory/theories/conjectures/implications_X228.v). *)

From GraphTheory Require Import mgraph.
From mathcomp Require Import boot order algebra.
From GC.GraphLib Require Import cycle flow.
From GC.cycle.AX_bridgeless_2_flow_4_flow_pair Require Import
  main(AX_bridgeless_2_flow_4_flow_pair).
From GC.cycle.OPG_nowhere_zero_5_flow_bridgeless Require Import
  main(OPG_nowhere_zero_5_flow_bridgeless).

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Num.Theory Order.TTheory.

Local Open Scope ring_scope.

(** The values of [5 phi2 + phi4] lie between 2 and 8 in absolute value. *)
Lemma pair_bounds (a b : int) :
  `|a| <= 1 -> `|b| <= 3 -> (a = 0 -> 2 <= `|b|) -> 2 <= `|5 * a + b| <= 8.
Proof.
move=> a1 b3 a0; have [a_0|an0] := eqVneq a 0.
  by rewrite a_0 mulr0 add0r (a0 a_0) (le_trans b3).
have {}a1 : `|5 * a| = 5.
  rewrite normrM; have -> : `|a| = 1 by apply/eqP; rewrite eq_le a1 -[1]add0r lezD1 normr_gt0 an0.
  by rewrite mulr1.
apply/andP; split; last first.
  by apply: le_trans (ler_normD _ _) _; rewrite a1 (_ : 8 = 5 + 3) // lerD2l.
have := ler_normD (5 * a + b) (- b); rewrite addrK normrN a1 => h.
by rewrite -(lerD2r `|b|); apply: le_trans h; rewrite (_ : 5 = 2 + 3) // lerD2l.
Qed.

(** An integer whose double lies between 1 and 9 in absolute value lies between 1 and 4. *)
Lemma half_bounds (x : int) : 1 <= `|x * 2| <= 9 -> 1 <= `|x| <= 4.
Proof. by rewrite normrM -abszE; case: (absz x) => [|[|[|[|[|[]]]]]]. Qed.

Theorem AX_bridgeless_2_flow_4_flow_pair_implies_OPG_nowhere_zero_5_flow_bridgeless :
  AX_bridgeless_2_flow_4_flow_pair -> OPG_nowhere_zero_5_flow_bridgeless.
Proof.
move=> HP G E0 hbl; have [phi2 [phi4 [[c2 b2] [c4 b4] cmp]]] := HP G E0 hbl.
pose chi e := 5 * phi2 e + phi4 e.
have cchi : conservative chi.
  apply/conservativeE => v; rewrite mnetD mnetZ.
  by move/conservativeE: c2 => ->; move/conservativeE: c4 => ->; rewrite mulr0 addr0.
have mchi v : (2 %| mnet chi v)%Z by move/conservativeE: cchi => ->.
have [h [ch hb]] := @mod_flow_lift _ 2 chi isT mchi.
pose g e := ((chi e + h e) %/ 2)%Z.
have g2 e : g e * 2 = chi e + h e.
  apply: divzK; have [he _] := hb e.
  have -> : chi e + h e = (h e - chi e) + chi e * 2 by rewrite mulr_natr mulr2n addrA subrK addrC.
  by rewrite rpredD // dvdz_mull.
exists g; split.
  apply/conservativeE => v; apply: (mulIf (_ : 2 != 0)) => //; rewrite mul0r mulrC -mnetZ.
  have e2 : (fun e => 2 * g e) =1 (fun e => chi e + h e) by move=> e; rewrite mulrC g2.
  rewrite (eq_mnet e2) mnetD; move/conservativeE: cchi => ->; move/conservativeE: ch => ->.
  by rewrite addr0.
move=> e; apply/andP; apply: half_bounds; rewrite g2.
have [_ h2] := hb e; have /andP[lo hi] := pair_bounds (b2 e) (b4 e) (cmp e).
have h1 : `|h e| <= 1 by rewrite -ltzD1.
apply/andP; split; last by apply: le_trans (ler_normD _ _) _; rewrite (_ : 9 = 8 + 1) // lerD.
have := ler_normD (chi e + h e) (- h e); rewrite addrK normrN => hc.
rewrite -(lerD2r `|h e|); apply: le_trans hc; apply: le_trans lo.
by rewrite (_ : 2 = 1 + 1) // lerD2l.
Qed.


Check (AX_bridgeless_2_flow_4_flow_pair_implies_OPG_nowhere_zero_5_flow_bridgeless :
  GC.cycle.AX_bridgeless_2_flow_4_flow_pair.main.AX_bridgeless_2_flow_4_flow_pair ->
  GC.cycle.OPG_nowhere_zero_5_flow_bridgeless.main.OPG_nowhere_zero_5_flow_bridgeless).
Print Assumptions AX_bridgeless_2_flow_4_flow_pair_implies_OPG_nowhere_zero_5_flow_bridgeless.
