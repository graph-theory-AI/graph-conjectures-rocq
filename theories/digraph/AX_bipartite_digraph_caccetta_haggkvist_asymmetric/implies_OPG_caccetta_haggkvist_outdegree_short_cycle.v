(** * The asymmetric bipartite conjecture implies the Caccetta-Häggkvist conjecture

Let D be a digraph with n vertices and minimum out-degree at least r > 0.  The bipartite digraph H
on two copies of the vertices of D has an arc from (v,0) to (v,1) for each vertex v, and an arc
from (u,1) to (w,0) for each arc u -> w of D.  In H, each vertex of the side 0 has out-degree 1,
and each vertex of the side 1 has out-degree at least r.  The asymmetric conjecture applies with
β = 1/n, α = r/n and k = ⌈n/r⌉, since kα + β = (kr + 1)/n > 1, and gives a directed cycle of H of
length at most 2k.  Its vertices alternate between the two sides, and its vertices of the side 0
give a directed cycle of D of length at most k.

This is the derivation of the Caccetta-Häggkvist conjecture from Conjecture 1.5 in Seymour, Spirkl
(arXiv:1809.08324), the edge e101 of relations.json in graph-conjectures.  It was formalized in
graph-theory-rocq (digraph-theory/theories/conjectures/implications_P9.v). *)

From GraphTheory Require Import digraph connectivity.
From mathcomp Require Import boot order ssralg ssrnum rat zify_ssreflect.
From GC.digraph.AX_bipartite_digraph_caccetta_haggkvist_asymmetric Require Import
  main(AX_bipartite_digraph_caccetta_haggkvist_asymmetric).
From GC.digraph.OPG_caccetta_haggkvist_outdegree_short_cycle Require Import
  main(OPG_caccetta_haggkvist_outdegree_short_cycle).

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.Theory GRing.Theory Num.Theory.

Section Cover.
Variable D : diGraph.

(** The digraph H on [D * bool]: arcs from [(v, false)] to [(v, true)], and from [(u, true)] to
    [(w, false)] for each arc [u -- w] of [D]. *)
Definition cover : diGraph :=
  DiGraph [rel x y : D * bool | if x.2 then ~~ y.2 && (x.1 -- y.1) else y.2 && (y.1 == x.1)].

(** The vertices of the side [false] of a sequence of vertices of [cover], projected to [D]. *)
Definition proj (s : seq cover) : seq D := [seq x.1 | x <- s & ~~ x.2].

(** A walk of [cover] projects to a walk of [D] with half as many vertices. *)
Lemma path_proj (y : cover) s : path (--) y s ->
  path (--) y.1 (proj s) /\ size s + ~~ (last y s).2 = (size (proj s)).*2 + ~~ y.2.
Proof.
rewrite /proj; elim: s y => [|z s IH] y //= /andP[yz /IH[pz sz]].
case: y z yz {IH} pz sz => [u []] [v []]; rewrite [_ -- _]/edge_rel //=.
  by move=> -> -> sz; rewrite addSn sz addn0 addn1 doubleS.
by move/eqP => -> -> sz; rewrite addSn sz addn0 addn1.
Qed.

End Cover.

Theorem AX_bipartite_digraph_caccetta_haggkvist_asymmetric_implies_OPG_caccetta_haggkvist_outdegree_short_cycle :
  AX_bipartite_digraph_caccetta_haggkvist_asymmetric ->
  OPG_caccetta_haggkvist_outdegree_short_cycle.
Proof.
move=> HA D r n0 _ r0 deg; set n := #|D|; set k := (n + r - 1) %/ r.
have kr : n <= k * r by have := ltn_ceil (n + r - 1) r0; rewrite -/k mulSn; lia.
have k1 : 0 < k by rewrite divn_gt0 //; lia.
pose A : {set cover D} := setX [set: D] [set false].
have AC : ~: A = setX [set: D] [set true] by apply/setP => -[v []]; rewrite !inE.
have cA (b : bool) : #|setX [set: D] [set b]| = n by rewrite cardsX cardsT cards1 muln1.
have nR : (n%:R != 0 :> rat)%R by rewrite pnatr_eq0 -lt0n.
have [c [/andP[c0 /andP[cc uc]] sc]] : exists c : seq (cover D),
    (~~ nilp c && ucycleb (--) c) /\ size c <= 2 * k.
  apply: (HA rat k (r%:R / n%:R)%R (1 / n%:R)%R k1 _ _ _ _ A);
    try by apply: divr_gt0; rewrite ?ltr01 ?ltr0n.
  - rewrite mulrA -natrM -mulrDl natr1 ltr_pdivlMr ?ltr0n // mul1r ltr_nat; lia.
  - by rewrite -card_gt0 cA.
  - by rewrite -card_gt0 AC cA.
  - by move=> [u [] [w []]]; rewrite [_ -- _]/edge_rel /= !inE.
  - move=> [v []]; rewrite !inE //= AC cA mulfVK // => _; rewrite ler1n card_gt0.
    by apply/set0Pn; exists (v, true); rewrite in_opn [_ -- _]/edge_rel /= eqxx.
  - move=> [u []]; rewrite !inE //= cA mulfVK // => _; rewrite ler_nat.
    have inj : injective (fun w : D => (w, false) : cover D) by move=> w w' [].
    apply: leq_trans (deg u) _; change (#|N(u)| <= #|N((u, true) : cover D)|).
    rewrite -(card_imset _ inj); apply/subset_leq_card/subsetP => _ /imsetP[w uw ->].
    by rewrite in_opn [_ -- _]/edge_rel /= -in_opn.
have [y yc /negPf y2] : exists2 y, y \in c & ~~ y.2.
  case: c c0 cc {uc sc} => // x s _ cc; case x2: x.2; last by exists x; rewrite ?mem_head ?x2.
  exists (next (x :: s) x); first by rewrite mem_next mem_head.
  by have := next_cycle cc (mem_head x s); rewrite [_ -- _]/edge_rel /= x2 => /andP[].
case: y y2 yc => u _ /= -> /rot_to[i s cE].
move: cc uc sc; rewrite -(rot_cycle i) -(rot_uniq i) -(size_rot i) cE => cc uc sc.
have [pu su] := path_proj cc; rewrite /proj filter_rcons map_rcons in pu su.
exists (u :: proj s); split; last by move: su sc; rewrite /proj /= !size_rcons /=; lia.
apply/and3P; split => //; rewrite (_ : u :: _ = proj ((u, false) :: s)) //.
rewrite /proj map_inj_in_uniq ?filter_uniq // => -[v b] [w b'].
by rewrite !mem_filter /= => /andP[/negPf -> _] /andP[/negPf -> _] /= ->.
Qed.

Check (AX_bipartite_digraph_caccetta_haggkvist_asymmetric_implies_OPG_caccetta_haggkvist_outdegree_short_cycle :
  GC.digraph.AX_bipartite_digraph_caccetta_haggkvist_asymmetric.main.AX_bipartite_digraph_caccetta_haggkvist_asymmetric ->
  GC.digraph.OPG_caccetta_haggkvist_outdegree_short_cycle.main.OPG_caccetta_haggkvist_outdegree_short_cycle).
Print Assumptions AX_bipartite_digraph_caccetta_haggkvist_asymmetric_implies_OPG_caccetta_haggkvist_outdegree_short_cycle.
