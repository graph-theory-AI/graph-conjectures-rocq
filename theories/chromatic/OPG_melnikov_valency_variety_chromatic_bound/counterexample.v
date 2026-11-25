(** * A graph with 37 vertices, 30 different degrees and a 3-colouring

The graph is 3-partite.  Two vertices of different classes are adjacent when the sum of their
weights is at least 18, where the weights in the three classes are
- 4, 5, ..., 11, eight times 12, 15, 16, 17 (19 vertices),
- 0, 2, 12, 13, 14, 15, 17, 18 (8 vertices),
- 0, 1, 3, 6, 7, ..., 12 (10 vertices).
Its degrees are 0, 1, ..., 29.  So its valency-variety is 30, and the claimed strict lower bound
on the chromatic number is ⌈15 / 7⌉ = 3, while the graph is 3-colourable.

Another graph with these properties comes from Graph-Theory-LLM-Proofs
(attacks_opg/melnikovs_valency_variety_problem) and was formalized in graph-theory-rocq
(chromatic-theory/theories/applications/melnikov_valency_variety.v).  The graph above has a
similar structure, with a shorter description that makes the 3-colouring immediate.  Both have
an isolated vertex, which the problem allows. *)

From GraphTheory Require Import preliminaries digraph sgraph coloring.
From GC.GraphLib Require Import chromatic.
From GC.chromatic.OPG_melnikov_valency_variety_chromatic_bound Require main.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Abbreviation valency_variety := main.valency_variety.

(** The class of vertex [x], used as its colour. *)
Definition class (x : nat) : 'I_3 :=
  if x < 19 then ord0 else if x < 27 then preliminaries.ord1 else preliminaries.ord2.

Definition weights : seq nat :=
  iota 4 8 ++ nseq 8 12 ++ [:: 15; 16; 17] ++
  [:: 0; 2; 12; 13; 14; 15; 17; 18] ++
  [:: 0; 1; 3] ++ iota 6 7.

Definition adj (x y : nat) : bool :=
  (class x != class y) && (18 <= nth 0 weights x + nth 0 weights y).

Lemma adj_sym : symmetric (relpre (val : 'I_37 -> nat) adj).
Proof. by move=> x y; rewrite /= /adj eq_sym addnC. Qed.

Lemma adj_irrefl : irreflexive (relpre (val : 'I_37 -> nat) adj).
Proof. by move=> x; rewrite /= /adj eqxx. Qed.

Definition threshold_graph : sgraph := SGraph adj_sym adj_irrefl.

Lemma chi_threshold_graph : χ([set: threshold_graph]) <= 3.
Proof.
by apply/chi_leP; exists (class \o val); apply/proper_coloringP => x y /andP[].
Qed.

(** The degrees are computed on the list of the 37 vertices. *)
Lemma valency_variety_threshold_graph : valency_variety threshold_graph = 30.
Proof.
pose deg x := count (adj x) (iota 0 37).
have degE (x : threshold_graph) : #|N(x)| = deg (val x).
  by rewrite /deg -val_enum_ord count_map cardsE cardE size_filter enumT.
rewrite /valency_variety enum_setT -enumT (eq_map degE) (map_comp deg) val_enum_ord.
by vm_compute.
Qed.

Lemma counterexample : ~ main.OPG_melnikov_valency_variety_chromatic_bound.
Proof.
move=> /(_ threshold_graph); rewrite card_ord valency_variety_threshold_graph => /(_ isT).
by rewrite ltnNge chi_threshold_graph.
Qed.
