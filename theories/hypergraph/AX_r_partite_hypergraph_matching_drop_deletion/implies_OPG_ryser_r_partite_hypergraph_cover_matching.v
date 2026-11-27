(** * The matching drop by deletion conjecture implies Ryser's conjecture

Let H be an r-partite r-uniform hypergraph with matching number ν.  By induction on ν, H has a
vertex cover with at most (r - 1)ν vertices.  If H has no edge, the empty set is a cover.
Otherwise, the deletion conjecture gives k >= 1 and a set X of k(r - 1) vertices whose deletion
leaves a hypergraph H' (again r-partite r-uniform) with matching number ν' <= ν - k.  By
induction, H' has a cover Y with at most (r - 1)ν' vertices, and X ∪ Y covers H: an edge that
avoids X is an edge of H'.  It has at most k(r - 1) + (r - 1)ν' <= (r - 1)ν vertices.

The implication is stated by Clow, Haxell and Mohar (arXiv:2505.05339), and is the edge e144 of
relations.json in graph-conjectures.  It was formalized in graph-theory-rocq
(hypergraph-theory/theories/conjectures/implications_U12.v). *)

From mathcomp Require Import boot.
From GC.GraphLib Require Import hypergraph.
From GC.hypergraph.AX_r_partite_hypergraph_matching_drop_deletion Require Import
  main(AX_r_partite_hypergraph_matching_drop_deletion).
From GC.hypergraph.OPG_ryser_r_partite_hypergraph_cover_matching Require Import
  main(OPG_ryser_r_partite_hypergraph_cover_matching).

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Under the deletion conjecture, an r-partite r-uniform hypergraph with matching number [nu] has a
    vertex cover with at most [(r - 1) * nu] vertices. *)
Lemma cover_by_deletion (r : nat) (T : finType) (part : T -> 'I_r) :
  AX_r_partite_hypergraph_matching_drop_deletion -> 1 < r ->
  forall (E : {set {set T}}) (nu : nat), hg_partite_uniform part E -> hg_matching_number E nu ->
  exists X : {set T}, hg_cover X E /\ #|X| <= (r - 1) * nu.
Proof.
move=> AX r1 E nu; elim/ltn_ind: nu E => nu IH E Ep Enu.
have [->|E0] := eqVneq E set0.
  by exists set0; rewrite cards0; split=> // e; rewrite inE.
have [k [X [k1 _ cardX [nu' [Enu' le_k]]]]] := AX r T part E nu r1 E0 Ep Enu.
have Ep' : hg_partite_uniform part (hg_restrict E (~: X)) by move=> e; rewrite inE => /andP[/Ep].
have [|Y [covY cardY]] := IH nu' _ _ Ep' Enu'.
  by rewrite (leq_trans _ le_k) // -addn1 leq_add2l.
exists (X :|: Y); split=> [e eE|].
  rewrite setIUl setU_eq0 negb_and; have [eX|] := boolP (e \subset ~: X).
    by rewrite covY ?orbT // inE eE eX.
  by rewrite subsets_disjoint setCK -setI_eq0 setIC => ->.
apply: leq_trans (leq_card_setU X Y) _; rewrite cardX.
apply: leq_trans (leq_add (leqnn _) cardY) _.
by rewrite mulnC -mulnDr leq_mul2l addnC le_k orbT.
Qed.

Theorem AX_r_partite_hypergraph_matching_drop_deletion_implies_OPG_ryser_r_partite_hypergraph_cover_matching :
  AX_r_partite_hypergraph_matching_drop_deletion -> OPG_ryser_r_partite_hypergraph_cover_matching.
Proof.
move=> AX r T part E nu tau r1 Ep Enu [_ tau_min].
have [X [covX cardX]] := cover_by_deletion AX r1 Ep Enu.
exact: leq_trans (tau_min X covX) cardX.
Qed.

Check (AX_r_partite_hypergraph_matching_drop_deletion_implies_OPG_ryser_r_partite_hypergraph_cover_matching :
  GC.hypergraph.AX_r_partite_hypergraph_matching_drop_deletion.main.AX_r_partite_hypergraph_matching_drop_deletion ->
  GC.hypergraph.OPG_ryser_r_partite_hypergraph_cover_matching.main.OPG_ryser_r_partite_hypergraph_cover_matching).
Print Assumptions AX_r_partite_hypergraph_matching_drop_deletion_implies_OPG_ryser_r_partite_hypergraph_cover_matching.
