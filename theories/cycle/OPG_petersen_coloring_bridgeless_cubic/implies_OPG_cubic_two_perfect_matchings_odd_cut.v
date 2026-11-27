(** * The Petersen colouring conjecture implies the conjecture on the intersection of two perfect
    matchings

Composition of two implications: the Petersen colouring conjecture implies the Berge-Fulkerson
conjecture (by pulling back the six perfect matchings of the Petersen graph), which implies the
conjecture on the intersection of two perfect matchings (a perfect matching of a cubic graph meets
every odd cut).

The implication was formalized in graph-theory-rocq
(cycle-theory/theories/conjectures/implications_U10.v). *)

From GC.cycle.OPG_petersen_coloring_bridgeless_cubic Require Import
  implies_OPG_berge_fulkerson_cubic_6_perfect_matchings(
    OPG_petersen_coloring_bridgeless_cubic_implies_OPG_berge_fulkerson_cubic_6_perfect_matchings).
From GC.cycle.OPG_berge_fulkerson_cubic_6_perfect_matchings Require Import
  implies_OPG_cubic_two_perfect_matchings_odd_cut(
    OPG_berge_fulkerson_cubic_6_perfect_matchings_implies_OPG_cubic_two_perfect_matchings_odd_cut).
From GC.cycle.OPG_petersen_coloring_bridgeless_cubic Require Import
  main(OPG_petersen_coloring_bridgeless_cubic).
From GC.cycle.OPG_cubic_two_perfect_matchings_odd_cut Require Import
  main(OPG_cubic_two_perfect_matchings_odd_cut).

Theorem OPG_petersen_coloring_bridgeless_cubic_implies_OPG_cubic_two_perfect_matchings_odd_cut :
  OPG_petersen_coloring_bridgeless_cubic -> OPG_cubic_two_perfect_matchings_odd_cut.
Proof.
intro coloring.
apply OPG_berge_fulkerson_cubic_6_perfect_matchings_implies_OPG_cubic_two_perfect_matchings_odd_cut.
apply OPG_petersen_coloring_bridgeless_cubic_implies_OPG_berge_fulkerson_cubic_6_perfect_matchings.
exact coloring.
Qed.

Check (OPG_petersen_coloring_bridgeless_cubic_implies_OPG_cubic_two_perfect_matchings_odd_cut :
  GC.cycle.OPG_petersen_coloring_bridgeless_cubic.main.OPG_petersen_coloring_bridgeless_cubic ->
  GC.cycle.OPG_cubic_two_perfect_matchings_odd_cut.main.OPG_cubic_two_perfect_matchings_odd_cut).

Print Assumptions
  OPG_petersen_coloring_bridgeless_cubic_implies_OPG_cubic_two_perfect_matchings_odd_cut.
