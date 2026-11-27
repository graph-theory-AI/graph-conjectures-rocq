(** * The Petersen colouring conjecture implies the 5-cycle double cover conjecture

The Petersen graph has a double cover by five even subgraphs.  It is given by a label for each
edge, the 2-subset of {0,...,4} of the indices of the subgraphs that contain it, such that the
three labels at each vertex are the three 2-subsets of a 3-set: then each subgraph contains 0 or 2
edges at each vertex.  A Petersen colouring [f] of a bridgeless loopless cubic graph [G] maps the
three edges at a vertex of [G] to three pairwise adjacent edges of the Petersen graph, which have
a common end ([petersen_claw]).  Hence the preimages by [f] of the five subgraphs form a double
cover of [G] by five even subgraphs.  The 5-cycle double cover conjecture follows by the classical
reduction to cubic graphs ([cubic_reduction]).

The labels are given by a table on 5-bit codes of the vertices of the Petersen graph, and the
finite checks are computations on these codes.

The implication is the edge e090 of relations.json in graph-conjectures.  It was formalized in
graph-theory-rocq (cycle-theory/theories/conjectures/implications_U6.v). *)

From GraphTheory Require Import mgraph.
From mathcomp Require Import boot.
From GC.GraphLib Require Import misc cycle even_subgraph.
From GC.cycle.OPG_bridgeless_cycle_double_cover_5_cycles Require Import cubic_reduction.
From GC.cycle.OPG_petersen_coloring_bridgeless_cubic Require Import petersen_claws.
From GC.cycle.OPG_petersen_coloring_bridgeless_cubic Require Import
  main(OPG_petersen_coloring_bridgeless_cubic).
From GC.cycle.OPG_bridgeless_cycle_double_cover_5_cycles Require Import
  main(OPG_bridgeless_cycle_double_cover_5_cycles).

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** A double cover of the Petersen graph by five even subgraphs *)

(** [table a b], for the codes [a < b] of two adjacent vertices, is the code of the label of the
    edge between them. *)
Definition table (a b : nat) : nat :=
  match a, b with
  | 3, 12 => 3 | 3, 20 => 5 | 3, 24 => 6 | 5, 10 => 3 | 5, 18 => 9
  | 5, 24 => 10 | 6, 9 => 20 | 6, 17 => 24 | 6, 24 => 12 | 9, 18 => 24
  | 9, 20 => 12 | 10, 17 => 10 | 10, 20 => 9 | 12, 17 => 18 | 12, 18 => 17
  | _, _ => 0
  end.

Definition labc (a b : nat) : nat := table (minn a b) (maxn a b).

Lemma label_check : all (fun c => all (fun d => popc (labc c d) == 2) (nbr c)) C2.
Proof. by compute. Qed.

Lemma claw_check :
  all (fun c => all (fun d1 => all (fun d2 => all (fun d3 =>
      [&& d1 != d2, d2 != d3 & d1 != d3] ==>
      all (fun k => ~~ odd (bit k (labc c d1) + bit k (labc c d2) + bit k (labc c d3)))
        (iota 0 5))
    (nbr c)) (nbr c)) (nbr c)) C2.
Proof. by compute. Qed.

(** The label of an edge, from its ends. *)
Definition labelX (X Y : {set 'I_5}) : {set 'I_5} :=
  [set i : 'I_5 | bit i (labc (code X) (code Y))].
Definition label (q : petersen_edge) : {set 'I_5} := labelX (val (val q).1) (val (val q).2).

(** Each edge is in two subgraphs of the cover. *)
Lemma card_label (q : petersen_edge) : #|label q| = 2.
Proof.
rewrite /label /labelX card_bits; have a : petersen_adj (val q).1 (val q).2 := valP q.
by move/allP: label_check => /(_ _ (code_V (val q).1)) /allP /(_ _ (code_nbr a)) /eqP.
Qed.

Lemma label_ends (q : petersen_edge) (p y : petersenV) :
  petersen_ends q = [set p; y] -> label q = labelX (val p) (val y).
Proof.
move=> e; have n := petersen_adj_neq (valP q).
have : (val q).1 \in [set p; y] by rewrite -e !inE eqxx.
have : (val q).2 \in [set p; y] by rewrite -e !inE eqxx orbT.
rewrite /label !inE => /orP[] /eqP h2 /orP[] /eqP h1.
all: rewrite h1 h2 ?eqxx // in n *; by rewrite /labelX /labc minnC maxnC.
Qed.

(** Each subgraph of the cover contains 0 or 2 edges of a claw. *)
Lemma label_claw_even (q1 q2 q3 : petersen_edge) (i : 'I_5) :
  mutually_adjacent petersen_edge_adj q1 q2 q3 ->
  ~~ odd ((i \in label q1) + (i \in label q2) + (i \in label q3)).
Proof.
move=> /petersen_claw [p [y1 [y2 [y3 [e1 e2 e3 [a1 a2 a3] [d12 d23 d13]]]]]].
rewrite (label_ends e1) (label_ends e2) (label_ends e3) !inE.
have d (y y' : petersenV) : y != y' -> code (val y) != code (val y').
  by apply: contraNneq => /code_inj/val_inj ->.
move/allP: claw_check => /(_ _ (code_V p)) /allP /(_ _ (code_nbr a1)) /allP
  /(_ _ (code_nbr a2)) /allP /(_ _ (code_nbr a3)).
rewrite (d _ _ d12) (d _ _ d23) (d _ _ d13) => /implyP /(_ isT) /allP; apply.
by rewrite mem_iota ltn_ord.
Qed.

(** ** Pulling back the cover along a Petersen colouring *)

Section Pullback.
Variables (G : mgraph) (f : edge G -> petersen_edge).
Hypothesis Gc : loopless_cubic G.
Hypothesis fc : forall e1 e2 e3 : edge G, mutually_adjacent (@mline_rel G) e1 e2 e3 ->
  mutually_adjacent petersen_edge_adj (f e1) (f e2) (f e3).

Definition pull (i : 'I_5) : {set edge G} := [set e | i \in label (f e)].

Lemma pull_even i : even_subgraph (pull i).
Proof.
move=> v; case: Gc => ll cub; rewrite mdeg_in_loopless //.
have /card_gt0P[e1 e1v] : 0 < #|edges_at v| by rewrite cub.
have /cards2P[e2 [e3 [n23 E]]] : #|edges_at v :\ e1| == 2.
  by move: (cub v); rewrite (cardsD1 e1) e1v add1n => -[->].
have : e2 \in edges_at v :\ e1 by rewrite E !inE eqxx.
have : e3 \in edges_at v :\ e1 by rewrite E !inE eqxx orbT.
rewrite !inE => /andP[n13 e3v] /andP[n12 e2v].
have adj a b : incident v a -> incident v b -> a != b -> mline_rel a b.
  by move=> av bv ab; rewrite /mline_rel ab /=; apply/existsP; exists v; rewrite av bv.
have e1v' : incident v e1 by rewrite inE in e1v.
have ma : mutually_adjacent (@mline_rel G) e1 e2 e3.
  by apply/and3P; split; apply: adj => //; rewrite eq_sym.
have := label_claw_even i (fc ma); rewrite -(setD1K e1v) E setIC -sum1_card.
under eq_bigl => e do rewrite in_setI.
rewrite big_mkcondr /= big_setU1 ?inE ?negb_or ?(eq_sym e1) ?n12 ?n13 //= big_setU1 ?inE //=.
by rewrite big_set1 !inE addnA.
Qed.

End Pullback.

Theorem OPG_petersen_coloring_bridgeless_cubic_implies_OPG_bridgeless_cycle_double_cover_5_cycles :
  OPG_petersen_coloring_bridgeless_cubic -> OPG_bridgeless_cycle_double_cover_5_cycles.
Proof.
move=> pc; apply: cubic_reduction => H H0 Hc bl; have [g gc] := pc H H0 (conj Hc bl).
exists (map (pull g) (enum 'I_5)); split.
- by rewrite size_map size_enum_ord.
- by move=> _ /mapP[i _ ->]; apply: pull_even.
- move=> e; rewrite count_map -[RHS](card_label (g e)) -sum1_count -sum1_card.
  by rewrite big_enum_cond /=; apply: eq_bigl => i; rewrite inE.
Qed.

Check (OPG_petersen_coloring_bridgeless_cubic_implies_OPG_bridgeless_cycle_double_cover_5_cycles :
  GC.cycle.OPG_petersen_coloring_bridgeless_cubic.main.OPG_petersen_coloring_bridgeless_cubic ->
  GC.cycle.OPG_bridgeless_cycle_double_cover_5_cycles.main.OPG_bridgeless_cycle_double_cover_5_cycles).

Print Assumptions
  OPG_petersen_coloring_bridgeless_cubic_implies_OPG_bridgeless_cycle_double_cover_5_cycles.
