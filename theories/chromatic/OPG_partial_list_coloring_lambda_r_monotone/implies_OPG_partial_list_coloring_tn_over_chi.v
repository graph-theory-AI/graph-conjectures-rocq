(** * Monotonicity of λ_t / t implies the partial list colouring conjecture

Let G be a graph with n vertices and choice number χ_l(G) = c, and let L be an assignment of lists
of t colours, with 1 <= t <= c (for t = 0 there is nothing to prove).  Since G is c-choosable, it is
coloured entirely from any lists of c colours, hence λ_c = n.  The ratio conjecture at r = t and
s = c gives t n = t λ_c <= c λ_t, and λ_t <= λ_L by definition of λ_t, where λ_L is the size of a
set W of vertices coloured from L.

In the constructive setting λ_t has to be shown to exist: the minimum ranges over all palettes.
Every assignment of lists of size t is relabelled into the palette {0, ..., t n} along a map
injective on the colours used; this keeps the sizes of the lists, and a set coloured from the new
lists is coloured from the old ones.  The minimum over the finitely many relabelled assignments is
then λ_t.

The implication is mentioned in the Open Problem Garden, and is the edge e000 of relations.json in
graph-conjectures.  It was formalized in graph-theory-rocq
(chromatic-theory/theories/conjectures/implications_U4.v). *)

From GraphTheory Require Import digraph sgraph.
From mathcomp Require Import boot.
From GC.GraphLib Require Import chromatic.
From GC.chromatic.OPG_partial_list_coloring_lambda_r_monotone Require Import
  main(OPG_partial_list_coloring_lambda_r_monotone).
From GC.chromatic.OPG_partial_list_coloring_tn_over_chi Require Import
  main(OPG_partial_list_coloring_tn_over_chi).

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Abbreviation colourable_count :=
  GC.chromatic.OPG_partial_list_coloring_lambda_r_monotone.main.colourable_count.
Abbreviation is_lambda := GC.chromatic.OPG_partial_list_coloring_lambda_r_monotone.main.is_lambda.

Section Lambda.
Variable G : sgraph.

(** The set [W] of vertices can be coloured from the lists [L], as a boolean. *)
Definition colorableb (C : finType) (L : G -> {set C}) (W : {set G}) : bool :=
  [exists f : {ffun induced W -> C},
     [forall v, f v \in L (val v)] && [forall x, [forall y, (x -- y) ==> (f x != f y)]]].

Lemma colorableP (C : finType) (L : G -> {set C}) (W : {set G}) :
  reflect (list_colorable (fun v : induced W => L (val v))) (colorableb L W).
Proof.
apply: (iffP existsP) => [[f /andP[/forallP fL /forallP fP]]|[f [fL fP]]].
  by exists f; split=> // x y; move/forallP: (fP x) => /(_ y) /implyP.
exists [ffun v => f v]; apply/andP; split; first by apply/forallP => v; rewrite ffunE.
by apply/forallP => x; apply/forallP => y; apply/implyP; rewrite !ffunE; apply: fP.
Qed.

(** λ_L: the maximum number of vertices coloured from [L]. *)
Definition lambda_L (C : finType) (L : G -> {set C}) : nat :=
  \max_(W | colorableb L W) #|W|.

Lemma lambda_LP (C : finType) (L : G -> {set C}) : colourable_count L (lambda_L L).
Proof.
have L0 : colorableb L set0.
  apply/colorableP; have no (v : induced (set0 : {set G})) : False by case: v => x; rewrite inE.
  by exists (fun v => False_rect C (no v)); split=> v; case: (no v).
split=> [|W /colorableP WL]; last exact: (leq_bigmax_cond _ WL).
exists [arg max_(W > set0 | colorableb L W) #|W|]; rewrite /lambda_L (bigmax_eq_arg _ L0).
by split=> //; apply/colorableP; case: arg_maxnP.
Qed.

(** Relabelling into the palette ['I_(t * #|G|).+1]. *)
Lemma relabel (t : nat) (C : finType) (L : G -> {set C}) : (forall v, #|L v| = t) ->
  exists L' : {ffun G -> {set 'I_(t * #|G|).+1}}, (forall v, #|L' v| = t) /\
    forall W, colorableb L' W -> colorableb L W.
Proof.
move=> Lt; pose U := \bigcup_v L v; pose s := enum U.
have LU v : L v \subset U by exact: bigcup_sup.
have sU : size s <= t * #|G|.
  apply: (@leq_trans (\sum_v #|L v|)); last first.
    by rewrite (eq_bigr _ (fun v _ => Lt v)) sum_nat_const mulnC.
  rewrite -cardE; apply: (big_ind2 (fun (A : {set C}) n => #|A| <= n)) => [|A m B n hA hB|//].
    by rewrite cards0.
  exact: leq_trans (leq_card_setU A B) (leq_add hA hB).
pose code (c : C) : 'I_(t * #|G|).+1 := inord (index c s).
have code_inj : {in U &, injective code}.
  move=> c d cU dU /(congr1 val); rewrite /= !inordK ?ltnS ?(leq_trans (index_size _ _) sU) //.
  by apply: (index_inj c); rewrite mem_enum.
exists [ffun v => code @: L v]; split=> [v|W /colorableP[f [fL fP]]].
  by rewrite ffunE card_in_imset ?Lt //; exact: (sub_in2 (subsetP (LU v)) code_inj).
have fi v : f v \in image code (L (val v)).
  by move: (fL v); rewrite ffunE => /imsetP[c cL ->]; exact: image_f.
apply/colorableP; exists (fun v => iinv (fi v)); split=> [v|x y xy]; first exact: mem_iinv.
by apply: contra (fP x y xy) => /eqP e; rewrite -(f_iinv (fi x)) -(f_iinv (fi y)) e.
Qed.

(** λ_t exists. *)
Lemma lambda_ex (t : nat) : exists lam, is_lambda G t lam.
Proof.
pose ok (m : nat) := [exists L : {ffun G -> {set 'I_(t * #|G|).+1}},
  [forall v, #|L v| == t] && (lambda_L L == m)].
have okP C (L : G -> {set C}) : (forall v, #|L v| = t) ->
    exists2 L' : {ffun G -> {set 'I_(t * #|G|).+1}}, ok (lambda_L L') & lambda_L L' <= lambda_L L.
  move=> /relabel[L' [L't L'L]]; exists L'.
    by apply/existsP; exists L'; rewrite eqxx andbT; apply/forallP => v; rewrite L't.
  by apply/bigmax_leqP => W /L'L; exact: leq_bigmax_cond.
have [L' okL' _] := okP _ (fun _ : G => [set: 'I_t]) (fun _ => etrans (cardsT _) (card_ord t)).
have [lam /existsP[L0 /andP[/forallP L0t /eqP <-]] lmin] := ex_minnP (ex_intro ok _ okL').
exists (lambda_L L0); split.
  by exists _, L0; split=> [v|]; [apply/eqP | exact: lambda_LP].
move=> C L mu Lt [_ ub]; have [L1 okL1 le1] := okP _ _ Lt.
apply: leq_trans (lmin _ okL1) (leq_trans le1 _).
by apply/bigmax_leqP => W /colorableP; exact: ub.
Qed.

End Lambda.

Theorem OPG_partial_list_coloring_lambda_r_monotone_implies_OPG_partial_list_coloring_tn_over_chi :
  OPG_partial_list_coloring_lambda_r_monotone -> OPG_partial_list_coloring_tn_over_chi.
Proof.
move=> mono G t cl icn tcl C L Lt.
have [[W [WL cW]] _] := lambda_LP L; exists W; split=> //.
case: (posnP t) => [-> //|t_gt0].
have [lr lrP] := lambda_ex G t; have [ls lsP] := lambda_ex G cl.
have nls : #|G| <= ls.
  case: lsP => [[C' [L' [L'cl [_ ub]]]] _].
  have [f [fL fP]] := icn.1 C' L' (fun v => eq_leq (esym (L'cl v))).
  rewrite -cardsT; apply: ub; exists (fun v => f (val v)).
  by split=> [v|x y xy]; [exact: fL | exact: fP].
have key := mono G t cl cl lr ls icn t_gt0 tcl (leqnn cl) lrP lsP.
apply: leq_trans (leq_mul (leqnn t) nls) (leq_trans key _).
by rewrite leq_mul2l cW (proj2 lrP C L _ Lt (lambda_LP L)) orbT.
Qed.

Check (OPG_partial_list_coloring_lambda_r_monotone_implies_OPG_partial_list_coloring_tn_over_chi :
  GC.chromatic.OPG_partial_list_coloring_lambda_r_monotone.main.OPG_partial_list_coloring_lambda_r_monotone ->
  GC.chromatic.OPG_partial_list_coloring_tn_over_chi.main.OPG_partial_list_coloring_tn_over_chi).
Print Assumptions OPG_partial_list_coloring_lambda_r_monotone_implies_OPG_partial_list_coloring_tn_over_chi.
