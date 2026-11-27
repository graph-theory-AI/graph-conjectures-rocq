(** * The asymmetric bipartite conjecture implies the symmetric one

Let D be a bipartite digraph with n > 0 vertices in each part, in which every vertex has
out-degree more than n/(k+1), hence at least d = ⌊n/(k+1)⌋ + 1.  The asymmetric conjecture applies
with α = β = d/n, since kα + β = (k+1)d/n > 1, and gives a directed cycle of length at most 2k.

This is the derivation of Conjecture 1.2 from Conjecture 1.5 in Seymour, Spirkl (arXiv:1809.08324),
the edge e102 of relations.json in graph-conjectures.  It was formalized in graph-theory-rocq
(digraph-theory/theories/conjectures/implications_X46.v). *)

From GraphTheory Require Import digraph connectivity.
From mathcomp Require Import boot order ssralg ssrnum rat.
From GC.digraph.AX_bipartite_digraph_caccetta_haggkvist_asymmetric Require Import
  main(AX_bipartite_digraph_caccetta_haggkvist_asymmetric).
From GC.digraph.AX_bipartite_digraph_caccetta_haggkvist_girth Require Import
  main(AX_bipartite_digraph_caccetta_haggkvist_girth).

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.Theory GRing.Theory Num.Theory.

Theorem AX_bipartite_digraph_caccetta_haggkvist_asymmetric_implies_AX_bipartite_digraph_caccetta_haggkvist_girth :
  AX_bipartite_digraph_caccetta_haggkvist_asymmetric ->
  AX_bipartite_digraph_caccetta_haggkvist_girth.
Proof.
move=> H k n D A k1 n0 bipA cA cB deg.
pose d := (n %/ k.+1).+1; pose a : rat := (d%:R / n%:R)%R.
have aE : (a * n%:R = d%:R)%R by rewrite mulfVK // pnatr_eq0 -lt0n.
have degd (v : D) : d <= #|N(v)| by rewrite ltn_divLR // mulnC; apply: deg.
apply: (H _ k a a k1 _ _ _ D A _ _ bipA); rewrite ?divr_gt0 ?ltr0n // -?card_gt0 ?cA ?cB //;
  try by move=> v _; rewrite aE ler_nat degd.
rewrite -[X in (_ < _ + X)%R]mul1r -mulrDl natr1 mulrA -natrM.
by rewrite ltr_pdivlMr ?ltr0n // mul1r ltr_nat mulnC ltn_ceil.
Qed.

Check (AX_bipartite_digraph_caccetta_haggkvist_asymmetric_implies_AX_bipartite_digraph_caccetta_haggkvist_girth :
  GC.digraph.AX_bipartite_digraph_caccetta_haggkvist_asymmetric.main.AX_bipartite_digraph_caccetta_haggkvist_asymmetric ->
  GC.digraph.AX_bipartite_digraph_caccetta_haggkvist_girth.main.AX_bipartite_digraph_caccetta_haggkvist_girth).
Print Assumptions AX_bipartite_digraph_caccetta_haggkvist_asymmetric_implies_AX_bipartite_digraph_caccetta_haggkvist_girth.
