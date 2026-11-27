(** * The orientable 5-cycle double cover conjecture implies the 5-cycle double cover conjecture

Forgetting the orientations, the orientable conjecture gives a double cover by five even subgraphs
of every connected bridgeless graph.  A bridgeless graph [G] that is not connected is first made
connected: choose a vertex in each connected component (its root), and identify all the roots.
The resulting graph [K] has the same edges as [G]; it is connected and bridgeless.  An even
subgraph of [K] is an even subgraph of [G]: the degrees are the same at the vertices that are not
roots, and the degree of a root is the sum of the degrees in its component, which is even, minus
the degrees at the other vertices of the component.

The implication is the edge e238 of relations.json in graph-conjectures.  It was formalized in
graph-theory-rocq (cycle-theory/theories/conjectures/implications_U6.v). *)

From GraphTheory Require Import mgraph.
From mathcomp Require Import boot.
From GC.GraphLib Require Import misc cycle even_subgraph.
From GC.cycle.BM_bridgeless_cycle_double_cover_orientable_5 Require Import
  main(BM_bridgeless_cycle_double_cover_orientable_5).
From GC.cycle.OPG_bridgeless_cycle_double_cover_5_cycles Require Import
  main(OPG_bridgeless_cycle_double_cover_5_cycles).

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Collapse.
Variable G : mgraph.
Implicit Types (x y v : G).

(** ** Connected components *)

(** Two vertices are adjacent if an edge joins them. *)
Definition madj : rel G := fun x y =>
  [exists e : edge G, (source e == x) && (target e == y) || (source e == y) && (target e == x)].

Lemma madj_sym : symmetric madj.
Proof. by move=> x y; apply/existsP/existsP => -[e h]; exists e; rewrite orbC. Qed.

Lemma connect_uwalk x y : connect madj x y -> exists w, uwalk x y w.
Proof.
case/connectP => p; elim: p x => [x _ ->|z p IH x /= /andP[/existsP[e xz] pz] yl].
  by exists [::]; rewrite /= eqxx.
have [w hw] := IH z pz yl; exists (e :: w).
by move: hw; case/orP: xz => /andP[/eqP <- /eqP <-] hw; rewrite /= eqxx hw ?orbT.
Qed.

(** The root of the component of [x]. *)
Definition root x : G := odflt x [pick y | connect madj x y].

Lemma root_connect x : connect madj x (root x).
Proof. by rewrite /root; case: pickP. Qed.

Lemma root_eq x y : connect madj x y -> root x = root y.
Proof.
move=> xy; rewrite /root (eq_pick (_ : connect madj x =1 connect madj y)).
  move=> z; apply/idP/idP; last exact: connect_trans.
  by apply: connect_trans; rewrite (sym_connect_sym madj_sym).
by case: (pickP (connect madj y)) => //= /(_ y); rewrite connect0.
Qed.

Lemma root_root x : root (root x) = root x.
Proof. by rewrite -(root_eq (root_connect x)). Qed.

(** ** Identification of the roots *)

Variable r0 : G.
Hypothesis r0_root : root r0 = r0.

(** The vertices of [K] are the vertices of [G] that are not roots, and [r0]. *)
Definition kept v := (root v != v) || (v == r0).
Definition pr v := if root v == v then r0 else v.

Lemma kept_pr v : kept (pr v).
Proof. by rewrite /kept /pr; case: ifP => [_|->]; rewrite ?eqxx ?orbT. Qed.

Definition prj v : {v | kept v} := Sub (pr v) (kept_pr v).

Definition K : mgraph :=
  @Graph unit unit {v | kept v} (edge G) (fun b e => prj (endpoint b e)) (fun=> tt) (fun=> tt).

Lemma K_uwalk x y w : uwalk x y w -> @uwalk K (prj x) (prj y) w.
Proof.
elim: w x => [x /eqP -> |e w IH x /= /orP[] /andP[/eqP <- /IH h]]; rewrite /= ?eqxx //.
all: by rewrite h ?orbT.
Qed.

Lemma prj_val (u : K) : prj (val u) = u.
Proof.
apply: val_inj; rewrite /= /pr; case: ifP => // ru.
by have := valP u; rewrite /kept ru => /eqP.
Qed.

Lemma K_connected (u u' : K) : exists w, uwalk u u' w.
Proof.
have to_r0 (z : K) : exists w, @uwalk K z (prj r0) w.
  have [w /K_uwalk] := connect_uwalk (root_connect (val z)).
  have -> : prj (root (val z)) = prj r0.
    by apply: val_inj => /=; rewrite /pr root_root eqxx r0_root eqxx.
  by rewrite prj_val; exists w.
have [w1 h1] := to_r0 u; have [w2 h2] := to_r0 u'.
by exists (w1 ++ rev w2); apply: uwalk_cat h1 (uwalk_rev h2).
Qed.

Lemma K_medge_connected : bridgeless G -> medge_connected K 2.
Proof.
move=> bl; apply: mcut_medge_connected => S x y xS yS.
have [w hw] := K_connected x y.
have [|e _ eS] := uwalk_mcut (S := S) hw; first by rewrite xS (negbTE yS).
apply: bridgeless_mcut eS => f br; apply: (bl f) => w' /K_uwalk; exact: br.
Qed.

(** The degrees in [K] and in [G] are equal at a vertex that is not a root. *)
Lemma K_deg (C : {set edge G}) v (kv : kept v) :
  root v != v -> @mdeg_in K C (Sub v kv) = mdeg_in C v.
Proof.
move=> rv; have pr_eq w : (pr w == v) = (w == v).
  rewrite /pr; case: (eqVneq (root w) w) => [rw|//].
  by apply/eqP/eqP => [r0v|wv]; [rewrite -r0v r0_root in rv | rewrite -wv rw in rv];
    rewrite eqxx in rv.
by congr (_ + _); apply: eq_card => e; rewrite !inE -val_eqE /= pr_eq.
Qed.

(** An even subgraph of [K] is an even subgraph of [G]. *)
Lemma K_even (C : {set edge G}) : @even_subgraph K C -> even_subgraph C.
Proof.
move=> Ce v; have [rv|rv] := eqVneq (root v) v; last first.
  by rewrite -(K_deg C (_ : kept v) rv) ?Ce // /kept rv.
set S := [set y | connect madj v y]; have /(congr1 odd) := sum_mdeg_in C S.
have st f : (target f \in S) = (source f \in S).
  have sf : connect madj (source f) (target f).
    by apply: connect1; apply/existsP; exists f; rewrite !eqxx.
  rewrite !inE; apply/idP/idP => h; apply: connect_trans h _ => //.
  by rewrite (sym_connect_sym madj_sym).
under [X in _ = odd X]eq_bigr => f _ do rewrite st addnn -mul2n.
rewrite -big_distrr oddM /= (bigD1 v) ?inE ?connect0 //= oddD.
have -> : odd (\sum_(a in S | a != v) mdeg_in C a) = false.
  apply/negbTE; apply: (big_ind (fun n => ~~ odd n)) => [//|m n|a /andP[aS av]].
    by rewrite oddD => /negbTE -> /negbTE ->.
  have ra : root a != a by move: aS; rewrite inE => /root_eq <-; rewrite rv eq_sym.
  by rewrite -(K_deg C (_ : kept a) ra) ?Ce // /kept ra.
by rewrite addbF => ->.
Qed.

End Collapse.

Theorem BM_bridgeless_cycle_double_cover_orientable_5_implies_OPG_bridgeless_cycle_double_cover_5_cycles :
  BM_bridgeless_cycle_double_cover_orientable_5 -> OPG_bridgeless_cycle_double_cover_5_cycles.
Proof.
move=> orient G /card_gt0P[x0 _] _ bl; have r0_root := root_root x0.
have K0 : 0 < #|K (root x0)| by apply/card_gt0P; exists (prj (root x0) x0).
have [C [_ [Ce _ Cn _]]] := orient (K (root x0)) K0 (K_medge_connected r0_root bl).
exists (map C (enum 'I_5)); split.
- by rewrite size_map size_enum_ord.
- by move=> _ /mapP[i _ ->]; apply: K_even (Ce i).
- move=> e; rewrite count_map -[RHS](Cn e) -sum1_count -sum1_card.
  by rewrite big_enum_cond /=; apply: eq_bigl => i; rewrite inE.
Qed.

Check (BM_bridgeless_cycle_double_cover_orientable_5_implies_OPG_bridgeless_cycle_double_cover_5_cycles :
  GC.cycle.BM_bridgeless_cycle_double_cover_orientable_5.main.BM_bridgeless_cycle_double_cover_orientable_5 ->
  GC.cycle.OPG_bridgeless_cycle_double_cover_5_cycles.main.OPG_bridgeless_cycle_double_cover_5_cycles).

Print Assumptions
  BM_bridgeless_cycle_double_cover_orientable_5_implies_OPG_bridgeless_cycle_double_cover_5_cycles.
