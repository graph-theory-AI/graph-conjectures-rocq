(** * The Erdős–Lovász Tihany conjecture implies the double-critical graph conjecture

Let G be a connected double-critical graph with chromatic number k.

- If G has a clique K with at least k vertices, then every vertex v is in K.  Otherwise, v has a
  neighbour u, and the clique K - u avoids u and v, so that k - 1 <= χ(G - u - v) = k - 2.
  Hence G is complete.
- Otherwise, G has an edge (k >= 2), which is a clique, hence k >= 3.  The Erdős–Lovász Tihany
  conjecture with k + 1 = 2 + (k - 1) gives disjoint sets A and B with χ(A) = 2 and χ(B) = k - 1.
  An edge xy inside A gives k - 1 = χ(B) <= χ(G - x - y) = k - 2, a contradiction.

The implication is the edge e228 of relations.json in graph-conjectures.  It was formalized in
graph-theory-rocq (chromatic-theory/theories/conjectures/implications_U1.v). *)

From GraphTheory Require Import bij digraph sgraph dom coloring.
From mathcomp Require Import boot.
From GC.chromatic.BM_erdos_lovasz_tihany_disjoint_chromatic_split Require Import
  main(BM_erdos_lovasz_tihany_disjoint_chromatic_split).
From GC.chromatic.OPG_double_critical_graphs_are_complete Require Import
  main(OPG_double_critical_graphs_are_complete).

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** A set of chromatic number at least 2 contains an edge. *)
Lemma edge_of_chi (G : sgraph) (A : {set G}) :
  1 < χ(A) -> exists x y, [/\ x \in A, y \in A & x -- y].
Proof.
move=> chiA; apply/stablePn/negP => /(chiD1 A).
by rewrite setDv chi0 leqNgt chiA.
Qed.

Theorem
  BM_erdos_lovasz_tihany_disjoint_chromatic_split_implies_OPG_double_critical_graphs_are_complete :
  BM_erdos_lovasz_tihany_disjoint_chromatic_split -> OPG_double_critical_graphs_are_complete.
Proof.
move=> ELT G n G0 conG dc chiG; set k := χ([set: G]) in dc chiG.
have [v0 _] := card_gt0P G0.
have k1 : 0 < k by rewrite -(cards1 v0) -(chi_clique (@clique1 G v0)) sub_chi ?subsetT.
suff completeG : forall x y : G, x != y -> x -- y.
  have <- : #|G| = n by rewrite -chiG /k chi_clique ?cardsT // => x y _ _; apply: completeG.
  by constructor; apply: diso_Kn.
case: (boolP [exists K : {set G}, cliqueb K && (k <= #|K|)]) => [|/existsPn noK].
  (* a clique K with at least k vertices contains every vertex v *)
  case/existsP => K /andP[/cliqueP clK kK].
  suff KT : forall v, v \in K by move=> x y; apply: clK.
  move=> v; apply/negPn/negP => vK.
  have [w wK] := card_gt0P (leq_trans k1 kK).
  have [u vu] : exists u, v -- u.
    have /connectP[[|u p] /= pth lst] := conG v w (in_setT v) (in_setT w).
      by move: wK; rewrite lst (negbTE vK).
    by exists u; case/andP: pth => /andP[_ ->].
  have le : #|K :\ u| <= χ([set: G] :\: [set v; u]).
    rewrite -(chi_clique (cliqueD (H := [set u]) clK)) sub_chi //.
    apply/subsetP => x; rewrite !inE => /andP[/negbTE-> xK].
    by rewrite orbF andbT; apply: contraNneq vK => <-.
  move: kK; rewrite /k -(dc v u vu) (cardsD1 u K).
  by move/leq_trans/(_ (leq_add (leq_b1 _) le)); rewrite add1n addn2 ltnn.
(* no clique with k vertices: Erdős–Lovász Tihany with k + 1 = 2 + (k - 1) *)
have nocl (S : {set G}) : clique S -> #|S| < k.
  by move/cliqueP => clS; move: (noK S); rewrite clS ltnNge.
have k2 : 1 < k by have := nocl _ (@clique1 G v0); rewrite cards1.
have [u [v [_ _ uv]]] := edge_of_chi k2.
have k3 : 2 < k by have := nocl _ (clique2 uv); rewrite cards2 sg_edgeNeq.
have [|||A [B [dAB chiA chiB]]] := ELT G k 2 k.-1 erefl nocl.
- by rewrite addn1 add2n prednK.
- by [].
- by rewrite -ltnS prednK.
have /edge_of_chi[x [y [xA yA xy]]] : 1 < χ(A) by rewrite chiA.
have : B \subset [set: G] :\: [set x; y].
  apply/subsetP => b bB; rewrite !inE andbT.
  by apply: contraFN (disjointFl dAB bB) => /orP[]/eqP->.
by move/sub_chi; rewrite chiB -ltnS prednK // /k -(dc x y xy) addn2 ltnn.
Qed.

Check
  (BM_erdos_lovasz_tihany_disjoint_chromatic_split_implies_OPG_double_critical_graphs_are_complete :
GC.chromatic.BM_erdos_lovasz_tihany_disjoint_chromatic_split.main.BM_erdos_lovasz_tihany_disjoint_chromatic_split
  ->
GC.chromatic.OPG_double_critical_graphs_are_complete.main.OPG_double_critical_graphs_are_complete).
Print Assumptions
  BM_erdos_lovasz_tihany_disjoint_chromatic_split_implies_OPG_double_critical_graphs_are_complete.
