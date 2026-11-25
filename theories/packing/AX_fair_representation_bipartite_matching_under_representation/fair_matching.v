(** * A large matching that under-represents sets of edges in a bipartite graph

    Let G be a bipartite graph with maximum degree D > 0, and let E_0, ..., E_(m-1) be sets of
    edges.  Let L be large, and q = 2 ^ L / D (rounded down).  The multigraph consisting of [q]
    copies of each edge of G has maximum degree at most 2 ^ L.  Halving its degrees [L] times
    (see halving.v) provides a set of edges where the degrees are at most 1, i.e. a matching, with
    about q / 2 ^ L ~ 1 / D of the edges of G and of each E_i, up to a constant [err] that depends
    only on [m].  It remains to remove at most [err] edges of each E_i.

    This is a simplification of the proof of Graph-Theory-LLM-Proofs (attacks/1611.03196__03),
    which was formalized in graph-theory-rocq.  There, the edges are coloured with D colours by
    König's theorem, and the colour classes are then merged by pairs, with Alon's necklace splitting
    theorem.  Here, sets of edges are halved instead of merging matchings, so that the edges need
    not be coloured, and an approximate splitting with any bounded number of cuts is sufficient.
    The constant c(m) is cubic (instead of 12m + 14). *)

From GraphTheory Require Import digraph sgraph connectivity.
From GC.GraphLib Require Import misc.
From mathcomp Require Import boot.
From GC.packing.AX_fair_representation_bipartite_matching_under_representation
  Require main.
From GC.packing.AX_fair_representation_bipartite_matching_under_representation
  Require Import halving.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** The copies of the edges at a vertex *)

Section Ends.
Variables (G : sgraph) (B : {set G}).
Hypothesis bipB : bipartition B.

(** The rank of the end of [e] that is in [B]. *)
Definition end_in (e : {set G}) : nat := if [pick x in e :&: B] is Some x then enum_rank x else 0.

Lemma end_inE e x : e \in E(G) -> x \in e -> x \in B -> end_in e = enum_rank x.
Proof.
case/edgesP=> y [z [-> yz]] xe xB; have zB := bipB yz.
rewrite /end_in; case: pickP => [x' | /(_ x)]; last by rewrite inE xe xB.
move: xe xB; rewrite !inE => /orP[]/eqP-> xB /andP[/orP[]/eqP-> x'B] //; by rewrite xB x'B in zB.
Qed.

Lemma end_in_ex e : e \in E(G) -> exists2 x, x \in e & x \in B.
Proof.
case/edgesP=> y [z [-> yz]]; have := bipB yz; case: (boolP (y \in B)) => [yB _ | _ /esym/negbFE zB].
  by exists y; rewrite // set21.
by exists z; rewrite // set22.
Qed.

Definition edges_in (a : nat) : {set {set G}} := [set e in E(G) | end_in e == a].

Lemma card_edges_in e : e \in E(G) -> #|edges_in (end_in e)| <= Delta G.
Proof.
move=> eG; have [x xe xB] := end_in_ex eG.
apply: leq_trans (_ : #|N(x)| <= _); last exact: (leq_bigmax x).
apply: leq_trans (leq_imset_card (fun y => [set x; y]) _); apply/subset_leq_card/subsetP => e'.
rewrite inE => /andP[e'G]; have [x' x'e' x'B] := end_in_ex e'G.
rewrite (end_inE eG xe xB) (end_inE e'G x'e' x'B) => /eqP/val_inj/enum_rank_inj eq_x.
rewrite eq_x in x'e'; case/edgesP: e'G x'e' => y [z [-> yz]]; rewrite !inE => /orP[]/eqP eq_xy.
  by apply/imsetP; exists z; rewrite ?inE eq_xy.
by apply/imsetP; exists y; rewrite ?inE eq_xy 1?sgP // setUC.
Qed.

(** If there are [q] copies of each edge, the copies of the edges at a vertex [a] are numbered
    from [a * n], where [n] is any upper bound on their number. *)
Lemma copies (q n : nat) :
  q * Delta G <= n ->
  exists2 u : {set G} * 'I_q -> nat,
    {in [set x | x.1 \in E(G)] &, injective u} & {in E(G), forall e i, u (e, i) %/ n = end_in e}.
Proof.
move=> le_n; pose at_end a : {set {set G} * 'I_q} := setX (edges_in a) setT.
have mem_at e i : e \in E(G) -> (e, i) \in enum (at_end (end_in e)).
  by move=> eG; rewrite mem_enum !inE eG eqxx.
pose slot x := index x (enum (at_end (end_in x.1))).
have lt_slot e i : e \in E(G) -> slot (e, i) < n.
  move=> eG; apply: leq_trans le_n; apply: leq_trans (_ : #|at_end (end_in e)| <= _).
    by rewrite cardE index_mem mem_at.
  by rewrite cardsX cardsT card_ord mulnC leq_mul2l card_edges_in ?orbT.
pose u x := end_in x.1 * n + slot x.
have uE : {in E(G), forall e i, u (e, i) %/ n = end_in e}.
  move=> e eG i; have lt_n := lt_slot e i eG.
  by rewrite divnMDl ?divn_small ?addn0 // (leq_trans _ lt_n).
exists u => // -[e i] [e' i']; rewrite !inE /= => eG e'G eq_u.
have eq_e : end_in e = end_in e' by rewrite -(uE e eG i) -(uE e' e'G i') eq_u.
move/eqP: eq_u; rewrite /u /= eq_e eqn_add2l /slot /= eq_e => /eqP eq_s.
by apply: (index_inj (e, i) _ _ eq_s); rewrite ?mem_at // -eq_e mem_at.
Qed.

End Ends.

(** ** A matching with the right proportions *)

Section Proportion.
Variables (G : sgraph) (m : nat) (E : 'I_m -> {set {set G}}).
Hypotheses (bipG : bipartite G) (Delta_gt0 : 0 < Delta G) (E_sub : forall i, E i \subset E(G)).

Lemma proportional_matching :
  exists S : {set {set G}},
    [/\ matching S, #|E(G)| %/ Delta G <= #|S| + (err m.+1).+1
      & forall i, #|S :&: E i| <= #|E i| %/ Delta G + err m.+1].
Proof.
have [B bipB] := bipG; have bipB' : bipartition (~: B).
  by move=> x y xy; rewrite !inE (bipB _ _ xy) negbK.
pose L := #|E(G)|; pose q := 2 ^ L %/ Delta G.
have le_q : q * Delta G <= 2 ^ L by exact: leq_divM.
have [u inj_u uE] := copies bipB le_q; have [v inj_v vE] := copies bipB' le_q.
pose C j : {set {set G}} := if insub j is Some i then E i else E(G).
have CG j : C j \subset E(G) by rewrite /C; case: insubP => // i _ _; exact: E_sub.
pose A j := [set x : {set G} * 'I_q | x.1 \in C j].
have [Y [YX inj_uY inj_vY hY]] := halving_iter m.+1 A L inj_u inj_v.
have YG x : x \in Y -> x.1 \in E(G) by move/(subsetP YX); rewrite inE.
pose edge (x : {set G} * 'I_q) := x.1.
have inj1 : {in Y &, injective edge}.
  move=> [e i] [e' i'] xY yY; rewrite /edge /= => eq_e; apply: inj_uY => //.
  by rewrite (uE e (YG _ xY)) (uE e' (YG _ yY)) eq_e.
have cardX j : #|[set x : {set G} * 'I_q | x.1 \in E(G)] :&: A j| = #|C j| * q.
  rewrite -[q in RHS]card_ord -cardsT -cardsX; apply: eq_card => x.
  by rewrite !inE andbT andb_idl // => /(subsetP (CG j)).
have cardY j : #|Y :&: A j| = #|(edge @: Y) :&: C j|.
  rewrite -(card_in_imset (f := edge)).
    by move=> x y; rewrite !inE => /andP[xY _] /andP[yY _]; exact: inj1.
  apply: eq_card => e; apply/imsetP/setIP => [[x] | [/imsetP[x xY ->] xC]].
    by rewrite !inE => /andP[xY xC] ->; rewrite imset_f.
  by exists x; rewrite // !inE xY.
have L_gt0 : 0 < 2 ^ L by rewrite expn_gt0.
exists (edge @: Y); split.
- split=> [e /imsetP[x xY ->] | _ _ /imsetP[x xY ->] /imsetP[y yY ->] z zx zy]; first exact: YG.
  congr edge; have [zB | nzB] := boolP (z \in B).
    apply: inj_uY => //; rewrite [x]surjective_pairing [y]surjective_pairing.
    by rewrite !uE ?YG // (end_inE bipB (YG x xY) zx zB) (end_inE bipB (YG y yY) zy zB).
  have zB' : z \in ~: B by rewrite inE.
  apply: inj_vY => //; rewrite [x]surjective_pairing [y]surjective_pairing.
  by rewrite !vE ?YG // (end_inE bipB' (YG x xY) zx zB') (end_inE bipB' (YG y yY) zy zB').
- have [le_Y _] := hY m (ltnSn m); move: le_Y.
  have Cm : C m = E(G) by rewrite /C insubF ?ltnn.
  rewrite cardX cardY Cm => /(leq_trans (leq_addr _ _)) le_Y.
  have {}le_Y : #|E(G)| * q <= 2 ^ L * (#|edge @: Y| + err m.+1).
    by rewrite (leq_trans le_Y) // leq_mul2l leq_add2r subset_leq_card ?subsetIl ?orbT.
  have lt_q : 2 ^ L <= q.+1 * Delta G by rewrite ltnW // ltn_ceil.
  rewrite -(leq_pmul2l L_gt0) (leq_trans (leq_mul lt_q (leqnn _))) //.
  rewrite -mulnA [Delta G * _]mulnC (leq_trans (leq_mul (leqnn _) (leq_divM _ _))) //.
  rewrite mulSn addnS mulnS leq_add // ?(mulnC q) //; exact/ltnW/ltn_expl.
move=> i; have [_] := hY i (ltnW (ltn_ord i)).
have Ci : C i = E i by rewrite /C valK.
rewrite cardX cardY Ci => /(leq_trans (leq_addr _ _)); set y := #|_ :&: _| => le_y.
rewrite addnC -leq_subLR leq_divRL // -(leq_pmul2l L_gt0) mulnA mulnBr.
apply: leq_trans (_ : #|E i| * q * Delta G <= _).
  by rewrite leq_mul2r leq_subLR addnC le_y orbT.
by rewrite -mulnA [X in _ <= X]mulnC leq_mul2l le_q orbT.
Qed.

End Proportion.

(** ** Conclusion *)

Lemma under_representation :
  main.AX_fair_representation_bipartite_matching_under_representation.
Proof.
move=> m; exists (m * err m.+1 + (err m.+1).+1) => G E bipG D_gt0 E_sub.
have [S [matS le_S le_SE]] := proportional_matching bipG D_gt0 E_sub.
pose R i := [set e in take (err m.+1) (enum (S :&: E i))].
pose S' := S :\: \bigcup_i R i.
have S'S : S' \subset S by exact: subsetDl.
exists S'; split.
- case: matS => SG matS; split=> [e /(subsetP S'S)|]; first exact: SG.
  by move=> e f /(subsetP S'S) eS /(subsetP S'S); exact: matS.
- have le_R : #|\bigcup_i R i| <= m * err m.+1.
    apply: leq_trans (_ : \sum_(i < m) err m.+1 <= _); last by rewrite sum_nat_const card_ord.
    apply: (big_ind2 (fun (C : {set _}) n => #|C| <= n)) => [|C n C' n' le_C le_C'|i _].
    + by rewrite cards0.
    + exact: leq_trans (leq_card_setU _ _) (leq_add le_C le_C').
    by rewrite cardsE (leq_trans (card_size _)) // size_take_min geq_minl.
  apply: leq_trans le_S _; rewrite addnA leq_add2r -(cardsID (\bigcup_i R i) S) addnC leq_add2l.
  by rewrite (leq_trans _ le_R) // subset_leq_card ?subsetIr.
move=> i; apply: leq_trans (_ : #|E i| %/ Delta G <= _); last first.
  by rewrite /main.ceil_div leq_div2r // -addnBA // leq_addr.
apply: leq_trans (_ : #|[set e in drop (err m.+1) (enum (S :&: E i))]| <= _); last first.
  by rewrite cardsE (leq_trans (card_size _)) // size_drop -cardE leq_subLR addnC.
apply/subset_leq_card/subsetP => e; rewrite !inE => /andP[/andP[nR eS] eE].
set s := enum _; have : e \in take (err m.+1) s ++ drop (err m.+1) s.
  by rewrite cat_take_drop mem_enum inE eS.
rewrite mem_cat => /orP[eR|//].
by case/bigcupP: nR; exists i; rewrite // inE.
Qed.
