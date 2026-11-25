(** * A graph without two disjoint avoidable paths on 3 vertices

Main file of the disproof, for k = 3.  The graph G is the cycle 0 1 2 3 4 with an additional
vertex 5 adjacent to 0 and 1: it is the counterexample given by Bonamy, Defrain, Hatzel and
Thiebaut after their question, formalized in graph-theory-rocq
(graph-theory-misc/theories/applications/avoidable_paths_disproof.v).

The paths 1 2 3 and 4 0 5 are induced and disjoint.  An avoidable path on 3 vertices has an even
number of vertices in the triangle {0, 1, 5} [avoidable_even]: otherwise it is 1 2 3 or 0 4 3 (up
to reversal), with the extension 5 1 2 3 4 or 5 0 4 3 2, but no induced cycle contains 3 and 5
[no_cycle_3_5].  Two disjoint paths on 3 vertices contain together the three vertices of the
triangle, so they are not both avoidable. *)

From GraphTheory Require Import preliminaries digraph sgraph.
From GC.GraphLib Require Import misc.
From GC.misc.AX_avoidable_paths_two_disjoint_pk Require main.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Abbreviation avoidable_path := main.avoidable_path.

Definition G : sgraph :=
  edge_list_graph 6 [:: (0, 1); (1, 2); (2, 3); (3, 4); (4, 0); (5, 0); (5, 1)].

Abbreviation vtx i := (@Ordinal 6 i isT : G).

(** An induced cycle through a vertex of degree 2 contains its neighbours. *)
Lemma two_neighbours (c : seq G) u a b : chordless_cycle c -> u \in c ->
  (forall w, u -- w -> (w == a) || (w == b)) -> a \in c /\ b \in c.
Proof.
move=> cc uc nb; suff /eqP/setP e : N(u) :&: [set:: c] == [set a; b].
  by have := e a; have := e b; rewrite !inE !eqxx orbT => /andP[_ ->] /andP[_ ->].
rewrite eqEcard chordless_cycle_degree // cards2 ltnS leq_b1 andbT.
by apply/subsetP => w; rewrite !inE => /andP[/nb].
Qed.

(** An induced cycle through 3 contains 2 and 4, hence 1 and 0.  It does not contain 5, the third
    neighbour of 0. *)
Lemma no_cycle_3_5 (c : seq G) : chordless_cycle c -> vtx 3 \in c -> vtx 5 \notin c.
Proof.
move=> cc c3; have nbr u a b := @two_neighbours c u a b cc.
have [c2 c4] : vtx 2 \in c /\ vtx 4 \in c.
  by apply: nbr c3 _ => -[[|[|[|[|[|[|w]]]]]] ?].
have [c1 _] : vtx 1 \in c /\ vtx 3 \in c.
  by apply: nbr c2 _ => -[[|[|[|[|[|[|w]]]]]] ?].
have [_ c0] : vtx 3 \in c /\ vtx 0 \in c.
  by apply: nbr c4 _ => -[[|[|[|[|[|[|w]]]]]] ?].
apply/negP => c5; have := chordless_cycle_degree cc c0.
by rewrite (cardsD1 (vtx 1)) (cardsD1 (vtx 4)) (cardsD1 (vtx 5)) !inE c1 c4 c5.
Qed.

Lemma not_avoidable u v (p : seq G) : chordless_pathb (u :: rcons p v) ->
  vtx 3 \in u :: rcons p v -> vtx 5 \in u :: rcons p v -> ~ avoidable_path p.
Proof.
move=> /chordless_pathP ext e3 e5 [_ /(_ _ _ ext)[c [cc sub]]].
by have := no_cycle_3_5 cc (sub _ e3); rewrite sub.
Qed.

(** The triangle of G. *)
Definition T : seq G := [:: vtx 0; vtx 1; vtx 5].

(** By inspection of the induced paths: those with an odd number of vertices in the triangle are
    0 4 3, 1 2 3 and their reversals. *)
Lemma avoidable_even (p : seq G) : size p = 3 -> avoidable_path p -> ~~ odd (count (mem T) p).
Proof.
case: p => [|a [|b [|c [|]]]] //= _ av; have [/chordless_pathP/= + _] := av; move: av.
case: a => [[|[|[|[|[|[|a]]]]]] ?] //; case: b => [[|[|[|[|[|[|b]]]]]] ?] //;
  case: c => [[|[|[|[|[|[|c]]]]]] ?] //.
- by case/(not_avoidable (u := vtx 5) (v := vtx 2)).
- by case/(not_avoidable (u := vtx 5) (v := vtx 4)).
- by case/(not_avoidable (u := vtx 4) (v := vtx 5)).
- by case/(not_avoidable (u := vtx 2) (v := vtx 5)).
Qed.

(** Two disjoint paths on 3 vertices contain the three vertices of the triangle. *)
Lemma disjoint_count (p q : seq G) : uniq p -> uniq q -> size p = 3 -> size q = 3 ->
  [disjoint p & q] -> count (mem T) p + count (mem T) q = 3.
Proof.
move=> up uq sp sq; rewrite disjoint_sym disjoint_has => dis.
have upq : uniq (p ++ q) by rewrite cat_uniq up dis.
rewrite -count_cat; have /permP -> // : perm_eq (p ++ q) (vtx 2 :: vtx 3 :: vtx 4 :: T).
by apply: uniq_perm => // x; rewrite !ord_size_enum // size_cat sp sq.
Qed.

Theorem disproof : ~ main.AX_avoidable_paths_two_disjoint_pk.
Proof.
move=> /(_ 3 isT G)[[]|[p [q [sp sq ap aq dis]]]].
  exists [:: vtx 1; vtx 2; vtx 3], [:: vtx 4; vtx 0; vtx 5].
  by split; rewrite ?disjoint_has //; apply/chordless_pathP.
have [[[up _ _] _] [[uq _ _] _]] := (ap, aq).
have /(congr1 odd) := disjoint_count up uq sp sq dis.
by rewrite oddD (negbTE (avoidable_even sp ap)) (negbTE (avoidable_even sq aq)).
Qed.
