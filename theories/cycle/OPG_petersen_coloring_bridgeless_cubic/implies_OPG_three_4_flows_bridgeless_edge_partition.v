(** * The Petersen colouring conjecture implies the three 4-flows conjecture

The Petersen graph has six even subgraphs C(i,0), C(i,1) (i = 0, 1, 2) such that the classes
B_i = E \ (C(i,0) ∪ C(i,1)) partition its edges.  They are given by a label for each edge, the
set of the indices 2i + j of the subgraphs C(i,j) that contain it (as a 6-bit code); each C(i,j)
contains 0 or 2 edges of each claw.

Let [G] be a bridgeless graph, and [H] the loopless bridgeless cubic graph obtained by inflating
each vertex of [G] into a cycle ([inflate]).  A Petersen colouring [f] of [H] maps the three edges
at a vertex to a claw ([pull_claw]): the preimages by [f] of the six subgraphs are even subgraphs
of [H], and their contractions are even subgraphs of [G] ([contract_even]).  Let A_i be the set of
the edges of [G] whose copy is mapped into B_i.  The sets A_i partition the edges of [G], and the
contractions of C(i,0) and C(i,1) cover exactly the edges outside A_i: they give a nowhere-zero
4-flow of [G \ A_i] ([two_even_flow]).

The implication is the edge e032 of relations.json in graph-conjectures (Jaeger's reformulation
of the Petersen colouring conjecture).  It was formalized in graph-theory-rocq
(cycle-theory/theories/conjectures/implications_D1.v). *)

From GraphTheory Require Import mgraph.
From mathcomp Require Import boot.
From GC.GraphLib Require Import misc cycle cubic_inflation.
From GC.cycle.OPG_petersen_coloring_bridgeless_cubic Require Import
  petersen_claws petersen_labels even_flows.
From GC.cycle.OPG_petersen_coloring_bridgeless_cubic Require Import
  main(OPG_petersen_coloring_bridgeless_cubic).
From GC.cycle.OPG_three_4_flows_bridgeless_edge_partition Require Import
  main(OPG_three_4_flows_bridgeless_edge_partition).

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** [subgraphs a b], for the codes [a < b] of two adjacent vertices, is the code of the set of
    the indices of the subgraphs that contain the edge between them. *)
Definition subgraphs (a b : nat) : nat :=
  match a, b with
  | 3, 12 => 52 | 3, 20 => 6 | 3, 24 => 50 | 5, 10 => 44 | 5, 18 => 34
  | 5, 24 => 14 | 6, 9 => 24 | 6, 17 => 36 | 6, 24 => 60 | 9, 18 => 10
  | 9, 20 => 18 | 10, 17 => 56 | 10, 20 => 20 | 12, 17 => 28 | 12, 18 => 40
  | _, _ => 0
  end.

(** The edge of label [l] is in the class B_i. *)
Definition in_class (i l : nat) : bool := ~~ bit i.*2 l && ~~ bit i.*2.+1 l.

(** Each edge is in exactly one class. *)
Lemma subgraphs_check :
  edge_check subgraphs (fun l => in_class 0 l + in_class 1 l + in_class 2 l == 1).
Proof. by compute. Qed.

(** Each subgraph contains 0 or 2 edges of each claw. *)
Lemma subgraphs_claw_check : claw_check subgraphs
  (fun l1 l2 l3 => all (fun k => ~~ odd (bit k l1 + bit k l2 + bit k l3)) (iota 0 6)).
Proof. by compute. Qed.

Theorem OPG_petersen_coloring_bridgeless_cubic_implies_OPG_three_4_flows_bridgeless_edge_partition :
  OPG_petersen_coloring_bridgeless_cubic -> OPG_three_4_flows_bridgeless_edge_partition.
Proof.
move=> pc G /card_gt0P[e0 _] bl.
have H0 : 0 < #|inflate G| by apply/card_gt0P; exists (e0, false).
have Hc : loopless_cubic (inflate G) by split; [apply: inflate_loopless | apply: inflate_cubic].
have [f fc] := pc _ H0 (conj Hc (inflate_bridgeless bl)).
pose l (e : edge G) := plabel subgraphs (f (inl e)).
pose A i := [set e | in_class i (l e)].
have Ce k : k < 6 -> even_subgraph [set e | bit k (l e)].
  move=> k6; have -> : [set e | bit k (l e)] = contract [set a | bit k (plabel subgraphs (f a))].
    by apply/setP => e; rewrite !inE.
  apply: contract_even => v.
  apply: (pull_claw (P := fun q => bit k (plabel subgraphs q)) (Q := fun n => ~~ odd n) Hc fc).
  move=> q1 q2 q3 /(claw_checkP subgraphs_claw_check) /allP /(_ k).
  by rewrite mem_iota k6; apply.
have flow i : i < 3 -> nowhere_zero_flow (remove_edges (A i)) 4.
  move=> i3; apply: (@two_even_flow _ _ [set e | bit i.*2 (l e)] [set e | bit i.*2.+1 (l e)]).
  - by apply: Ce; rewrite -[6]/(3.*2) ltn_double.
  - by apply: Ce; rewrite -[6]/(3.*2) ltn_Sdouble.
  by move=> e; rewrite !inE negb_and !negbK.
have cls e : in_class 0 (l e) + in_class 1 (l e) + in_class 2 (l e) == 1.
  exact: (edge_checkP subgraphs_check (f (inl e))).
exists (A 0), (A 1), (A 2); split; last by split; apply: flow.
all: try (rewrite -setI_eq0; apply/eqP); apply/setP => e; rewrite !inE; move: (cls e).
all: by case: (in_class 0 (l e)); case: (in_class 1 (l e)); case: (in_class 2 (l e)).
Qed.

Check (
  OPG_petersen_coloring_bridgeless_cubic_implies_OPG_three_4_flows_bridgeless_edge_partition :
  GC.cycle.OPG_petersen_coloring_bridgeless_cubic.main.OPG_petersen_coloring_bridgeless_cubic ->
  GC.cycle.OPG_three_4_flows_bridgeless_edge_partition.main.OPG_three_4_flows_bridgeless_edge_partition).

Print Assumptions
  OPG_petersen_coloring_bridgeless_cubic_implies_OPG_three_4_flows_bridgeless_edge_partition.
