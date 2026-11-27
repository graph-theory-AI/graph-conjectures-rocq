(** * Δ(1,2,2) hero in complete multipartite implies Δ(1,2,2) hero without induced K_1 + P_2

An oriented digraph without induced K_1 + P_2 is an oriented complete multipartite graph: in its
underlying graph, non-adjacency is transitive, since vertices x, y, z with x, y non-adjacent, y, z
non-adjacent and x, z adjacent would induce K_1 + P_2; so the classes of non-adjacency are the
parts.  Hence the two classes of digraphs of the problems coincide (the converse inclusion is the
other implication), and the same bound on the dichromatic number holds.

The implication was formalized in graph-theory-rocq
(digraph-theory/theories/conjectures/implications_X221.v). *)

From GraphTheory Require Import preliminaries sgraph digraph.
From mathcomp Require Import boot.
From GC.digraph.AX_heroes_complete_multipartite_delta_1_2_2 Require Import
  main(AX_heroes_complete_multipartite_delta_1_2_2).
From GC.digraph.AX_heroes_delta_1_2_2_k1_p2_free Require Import
  main(AX_heroes_delta_1_2_2_k1_p2_free).

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Abbreviation oriented := GC.digraph.AX_heroes_complete_multipartite_delta_1_2_2.main.oriented.
Abbreviation underlying :=
  GC.digraph.AX_heroes_complete_multipartite_delta_1_2_2.main.underlying.
Abbreviation is_complete_multipartite :=
  GC.digraph.AX_heroes_complete_multipartite_delta_1_2_2.main.is_complete_multipartite.
Abbreviation k1_p2 := GC.digraph.AX_heroes_delta_1_2_2_k1_p2_free.main.k1_p2.

(** An oriented digraph without induced K_1 + P_2 has a complete multipartite underlying graph. *)
Lemma k1_p2_free_complete_multipartite (D : diGraph) :
  oriented D -> ~ inhabited (k1_p2 ⇀ D) -> is_complete_multipartite (underlying D).
Proof.
move=> orD noK; pose adj (x y : D) := x -- y || y -- x.
have loopF (x : D) : x -- x = false by apply/negP => xx; have := orD _ _ xx; rewrite xx.
have half x y z : ~~ adj x y -> ~~ adj y z -> ~~ (x -- z).
  move=> /norP[nxy nyx] /norP[nyz nzy]; apply/negP => xz.
  have xy : x != y by apply: contraTneq xz => ->; rewrite (negbTE nyz).
  have yz : y != z by apply: contraTneq xz => <-; rewrite (negbTE nxy).
  have xz' : x != z by apply: contraTneq xz => ->; rewrite loopF.
  pose f (v : k1_p2) : D := if v is inr i then (if i == ord0 then x else z) else y.
  apply: noK; apply: inhabits (@ISubgraph _ _ f _ _).
    by move=> [[[|//] ?]|[[|[|//]] ?]] [[[|//] ?]|[[|[|//]] ?]] //= e; apply/eqP;
       move: xy yz xz'; rewrite ?e ?eqxx.
  by move=> [[[|//] ?]|[[|[|//]] ?]] [[[|//] ?]|[[|[|//]] ?]] /=;
     rewrite ?loopF ?xz ?(negbTE nxy) ?(negbTE nyx) ?(negbTE nyz) ?(negbTE nzy)
             ?(negbTE (orD _ _ xz)).
have trans x y z : ~~ adj x y -> ~~ adj y z -> ~~ adj x z.
  by move=> nxy nyz; rewrite /adj negb_or (half _ _ _ nxy nyz) (half z y x) //; rewrite /adj orbC.
exists #|{set D}|, (fun x => enum_rank [set y | ~~ adj x y]) => x y.
have -> : x -- y = adj x y.
  by rewrite /edge_rel /= /sc; case: eqVneq => // ->; rewrite /adj loopF.
rewrite (inj_eq enum_rank_inj) -[adj x y]negbK; congr negb; apply/idP/eqP => [nxy|/setP/(_ y)].
  by apply/setP => z; rewrite !inE; apply/idP/idP; [apply: trans; rewrite /adj orbC | apply: trans].
by rewrite !inE /adj loopF.
Qed.

Theorem AX_heroes_complete_multipartite_delta_1_2_2_implies_AX_heroes_delta_1_2_2_k1_p2_free :
  AX_heroes_complete_multipartite_delta_1_2_2 -> AX_heroes_delta_1_2_2_k1_p2_free.
Proof.
move=> [n bnd]; exists n => D [orD noK noDelta]; apply: bnd; split=> //.
exact: k1_p2_free_complete_multipartite.
Qed.

Check (AX_heroes_complete_multipartite_delta_1_2_2_implies_AX_heroes_delta_1_2_2_k1_p2_free :
  GC.digraph.AX_heroes_complete_multipartite_delta_1_2_2.main.AX_heroes_complete_multipartite_delta_1_2_2 ->
  GC.digraph.AX_heroes_delta_1_2_2_k1_p2_free.main.AX_heroes_delta_1_2_2_k1_p2_free).
Print Assumptions
  AX_heroes_complete_multipartite_delta_1_2_2_implies_AX_heroes_delta_1_2_2_k1_p2_free.
