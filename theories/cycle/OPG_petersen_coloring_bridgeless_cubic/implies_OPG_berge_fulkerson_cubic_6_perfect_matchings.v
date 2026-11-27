(** * The Petersen colouring conjecture implies the Berge-Fulkerson conjecture

The Petersen graph has six perfect matchings, and every edge is in exactly two of them.  They are
given by a label for each edge, the 2-subset of {0,...,5} of the indices of the matchings that
contain it (as a 6-bit code).  Each matching contains exactly one edge of each claw.  A Petersen
colouring [f] of a bridgeless loopless cubic graph [G] maps the three edges at a vertex to a claw
([pull_claw]): hence the preimages by [f] of the six matchings are perfect matchings of [G], and
every edge of [G] is in exactly two of them.

The implication is due to Jaeger ("A survey of the cycle double cover conjecture", 1985).  It was
formalized in graph-theory-rocq (cycle-theory/theories/conjectures/implications_U10.v). *)

From GraphTheory Require Import mgraph.
From mathcomp Require Import boot.
From GC.GraphLib Require Import misc packing.
From GC.cycle.OPG_petersen_coloring_bridgeless_cubic Require Import petersen_claws petersen_labels.
From GC.cycle.OPG_petersen_coloring_bridgeless_cubic Require Import
  main(OPG_petersen_coloring_bridgeless_cubic).
From GC.cycle.OPG_berge_fulkerson_cubic_6_perfect_matchings Require Import
  main(OPG_berge_fulkerson_cubic_6_perfect_matchings).

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** [matchings a b], for the codes [a < b] of two adjacent vertices, is the code of the set of
    the indices of the matchings that contain the edge between them. *)
Definition matchings (a b : nat) : nat :=
  match a, b with
  | 3, 12 => 3 | 3, 20 => 12 | 3, 24 => 48 | 5, 10 => 20 | 5, 18 => 33
  | 5, 24 => 10 | 6, 9 => 40 | 6, 17 => 18 | 6, 24 => 5 | 9, 18 => 6
  | 9, 20 => 17 | 10, 17 => 9 | 10, 20 => 34 | 12, 17 => 36 | 12, 18 => 24
  | _, _ => 0
  end.

(** Each edge is in two matchings. *)
Lemma matchings_check : edge_check matchings (fun l => count (bit^~ l) (iota 0 6) == 2).
Proof. by compute. Qed.

(** Each matching contains one edge of each claw. *)
Lemma matchings_claw_check : claw_check matchings
  (fun l1 l2 l3 => all (fun k => bit k l1 + bit k l2 + bit k l3 == 1) (iota 0 6)).
Proof. by compute. Qed.

Theorem
  OPG_petersen_coloring_bridgeless_cubic_implies_OPG_berge_fulkerson_cubic_6_perfect_matchings :
  OPG_petersen_coloring_bridgeless_cubic -> OPG_berge_fulkerson_cubic_6_perfect_matchings.
Proof.
move=> pc G G0 [Gc bl]; have [f fc] := pc G G0 (conj Gc bl).
pose M (i : 'I_6) := [set e | bit i (plabel matchings (f e))].
exists (map M (enum 'I_6)); split.
- by rewrite size_map size_enum_ord.
- move=> _ /mapP[i _ ->] v.
  apply: (pull_claw (P := fun q => bit i (plabel matchings q)) (Q := eq^~ 1) Gc fc).
  move=> q1 q2 q3 /(claw_checkP matchings_claw_check) /allP /(_ i).
  by rewrite mem_iota ltn_ord => /(_ isT) /eqP.
- move=> e; rewrite count_map -[RHS](eqP (edge_checkP matchings_check (f e))).
  by rewrite -val_enum_ord count_map; apply: eq_count => i; rewrite /= inE.
Qed.

Check (
  OPG_petersen_coloring_bridgeless_cubic_implies_OPG_berge_fulkerson_cubic_6_perfect_matchings :
  GC.cycle.OPG_petersen_coloring_bridgeless_cubic.main.OPG_petersen_coloring_bridgeless_cubic ->
  GC.cycle.OPG_berge_fulkerson_cubic_6_perfect_matchings.main.OPG_berge_fulkerson_cubic_6_perfect_matchings).

Print Assumptions
  OPG_petersen_coloring_bridgeless_cubic_implies_OPG_berge_fulkerson_cubic_6_perfect_matchings.
