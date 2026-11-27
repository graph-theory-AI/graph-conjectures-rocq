(** * A Moore graph of degree 57 is an eighth triangle-free strongly regular graph

Let G be a 57-regular graph of diameter 2 and girth 5.  Two adjacent vertices have no common
neighbour (it would close a triangle), and two distinct nonadjacent vertices have a common
neighbour (diameter 2) and only one (two would close a 4-cycle).  Hence G is strongly regular
with parameters (57, 0, 1), and triangle-free.  Two adjacent vertices have 57 neighbours each
and none in common, so G has at least 114 vertices, while the seven known triangle-free strongly
regular graphs have at most 100 vertices: G is isomorphic to none of them.

The implication is the edge e147 of relations.json in graph-conjectures.  It was formalized in
graph-theory-rocq (atlas/theories/conjectures/implications_A1.v), where the seven graphs are
told apart by their degrees. *)

From GraphTheory Require Import digraph sgraph.
From mathcomp Require Import boot.
From GC.misc.OPG_moore_graph_degree_57_existence Require Import
  main(OPG_moore_graph_degree_57_existence).
From GC.spectral.OPG_strongly_regular_triangle_free_eighth Require Import
  main(OPG_strongly_regular_triangle_free_eighth).

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Abbreviation seq_cycle := GC.misc.OPG_moore_graph_degree_57_existence.main.seq_cycle.
Abbreviation girth_ge := GC.misc.OPG_moore_graph_degree_57_existence.main.girth_ge.
Abbreviation ball := GC.misc.OPG_moore_graph_degree_57_existence.main.ball.
Abbreviation common_neigh :=
  GC.spectral.OPG_strongly_regular_triangle_free_eighth.main.common_neigh.
Abbreviation strongly_regular :=
  GC.spectral.OPG_strongly_regular_triangle_free_eighth.main.strongly_regular.
Abbreviation known_triangle_free_srg :=
  GC.spectral.OPG_strongly_regular_triangle_free_eighth.main.known_triangle_free_srg.

Section Girth5.
Variables (G : sgraph) (girth5 : girth_ge G 5).

(** Adjacent vertices have no common neighbour. *)
Lemma adj_common_neigh (x y : G) : x -- y -> common_neigh x y = set0.
Proof.
move=> xy; apply/setP => z; rewrite !inE; apply/negP => /andP[xz yz].
have /girth5 // : seq_cycle (--) [:: x; y; z].
by rewrite /seq_cycle /ucycleb /= xy yz (sg_sym z) xz !inE !negb_or !sg_edgeNeq.
Qed.

(** Distinct nonadjacent vertices have at most one common neighbour. *)
Lemma nonadj_common_neigh_le1 (x y : G) : x != y -> #|common_neigh x y| <= 1.
Proof.
move=> xNy; apply/card_le1_eqP => w w'; rewrite !inE => /andP[xw yw] /andP[xw' yw'].
apply/eqP/negPn/negP => wNw'; have /girth5 // : seq_cycle (--) [:: x; w; y; w'].
rewrite /seq_cycle /ucycleb /= xw (sg_sym w) yw yw' (sg_sym w') xw' !inE !negb_or xNy.
by rewrite (eq_sym w w') wNw' (sg_edgeNeq xw) (sg_edgeNeq xw') eq_sym !sg_edgeNeq.
Qed.

End Girth5.

(** Distinct nonadjacent vertices at distance at most 2 have a common neighbour. *)
Lemma ball2_common_neigh (G : sgraph) (x y : G) :
  y \in ball 2 x -> x != y -> ~~ x -- y -> 0 < #|common_neigh x y|.
Proof.
move=> /= /bigcupP[z /bigcupP[_ /set1P-> xz] zy]; move: xz zy; rewrite !inE.
case/orP=> [/eqP->|xz] /orP[/eqP->|zy] xNy nxy; rewrite ?eqxx ?xz ?zy // in xNy nxy *.
by apply/card_gt0P; exists z; rewrite !inE xz sg_sym.
Qed.

Theorem OPG_moore_graph_degree_57_existence_implies_OPG_strongly_regular_triangle_free_eighth :
  OPG_moore_graph_degree_57_existence -> OPG_strongly_regular_triangle_free_eighth.
Proof.
move=> [G [reg [ball2 [u _]] [girth5 _]]].
have /card_gt0P[v uv] : 0 < #|N(u)| by rewrite reg.
have srg : strongly_regular G 57 0 1.
  split=> // x y; first by move=> xy; rewrite adj_common_neigh ?cards0.
  move=> xNy nxy; apply/eqP; rewrite eqn_leq nonadj_common_neigh_le1 //.
  exact: ball2_common_neigh.
exists G, 57, 0, 1; split.
  split=> //; first by apply/card_gt0P; exists u.
  move=> x y z xy yz zx; have /setP/(_ z) := adj_common_neigh girth5 xy.
  by rewrite !inE sg_sym zx yz.
move=> i [f]; have : 114 <= #|G|.
  apply: leq_trans (max_card (N(u) :|: N(v))); rewrite cardsU !reg.
  by rewrite inE in uv; rewrite -/(common_neigh u v) (adj_common_neigh girth5 uv) cards0.
rewrite (bij.card_bij f) ltnNge.
by case: i f => [[|[|[|[|[|[|[|//]]]]]]]] ? f; rewrite /= ?card_ord ?card_tuple ?card_bool.
Qed.

Check (OPG_moore_graph_degree_57_existence_implies_OPG_strongly_regular_triangle_free_eighth :
  GC.misc.OPG_moore_graph_degree_57_existence.main.OPG_moore_graph_degree_57_existence ->
  GC.spectral.OPG_strongly_regular_triangle_free_eighth.main.OPG_strongly_regular_triangle_free_eighth).
Print Assumptions
  OPG_moore_graph_degree_57_existence_implies_OPG_strongly_regular_triangle_free_eighth.
