(** * Δ(1,2,2) hero without induced K_1 + P_2 implies Δ(1,2,2) hero in complete multipartite

An oriented complete multipartite graph has no induced K_1 + P_2: a vertex non-adjacent to both
ends of an arc would be in the part of each end, so the two ends would be in the same part and
non-adjacent.  Hence the class of the second problem is contained in the class of the first, and
the same bound on the dichromatic number holds.

The implication is the edge e105 of relations.json in graph-conjectures.  It was formalized in
graph-theory-rocq (digraph-theory/theories/conjectures/implications_X221.v). *)

From GraphTheory Require Import preliminaries sgraph digraph.
From mathcomp Require Import boot.
From GC.digraph.AX_heroes_delta_1_2_2_k1_p2_free Require Import
  main(AX_heroes_delta_1_2_2_k1_p2_free).
From GC.digraph.AX_heroes_complete_multipartite_delta_1_2_2 Require Import
  main(AX_heroes_complete_multipartite_delta_1_2_2).

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Abbreviation k1_p2 := GC.digraph.AX_heroes_delta_1_2_2_k1_p2_free.main.k1_p2.
Abbreviation underlying :=
  GC.digraph.AX_heroes_complete_multipartite_delta_1_2_2.main.underlying.
Abbreviation is_complete_multipartite :=
  GC.digraph.AX_heroes_complete_multipartite_delta_1_2_2.main.is_complete_multipartite.

(** A digraph whose underlying graph is complete multipartite has no induced K_1 + P_2. *)
Lemma complete_multipartite_k1_p2_free (D : diGraph) :
  is_complete_multipartite (underlying D) -> ~ inhabited (k1_p2 ⇀ D).
Proof.
move=> [k [p pE]] [f].
have same x y : ~~ (x -- y) -> ~~ (y -- x) -> p (f x) = p (f y).
  move=> nxy nyx; apply/eqP; rewrite -[_ == _]negbK -pE /edge_rel /= /sc !isubgraph_mono.
  by rewrite (negbTE nxy) (negbTE nyx) andbF.
pose a : k1_p2 := inl ord0; pose b : k1_p2 := inr ord0; pose c : k1_p2 := inr ord_max.
have := pE (f b) (f c); rewrite -(same a b) // (same a c) // eqxx /edge_rel /= /sc.
by rewrite (inj_eq (isubgraph_inj f)) !isubgraph_mono.
Qed.

Theorem AX_heroes_delta_1_2_2_k1_p2_free_implies_AX_heroes_complete_multipartite_delta_1_2_2 :
  AX_heroes_delta_1_2_2_k1_p2_free -> AX_heroes_complete_multipartite_delta_1_2_2.
Proof.
move=> [n bnd]; exists n => D [orD cmD noDelta]; apply: bnd; split=> //.
exact: complete_multipartite_k1_p2_free.
Qed.

Check (AX_heroes_delta_1_2_2_k1_p2_free_implies_AX_heroes_complete_multipartite_delta_1_2_2 :
  GC.digraph.AX_heroes_delta_1_2_2_k1_p2_free.main.AX_heroes_delta_1_2_2_k1_p2_free ->
  GC.digraph.AX_heroes_complete_multipartite_delta_1_2_2.main.AX_heroes_complete_multipartite_delta_1_2_2).
Print Assumptions
  AX_heroes_delta_1_2_2_k1_p2_free_implies_AX_heroes_complete_multipartite_delta_1_2_2.
