(** * The directed Sidorenko conjecture implies Sidorenko's conjecture

Let H be a bipartite graph with sides A and its complement, with e edges and v vertices, and G a
graph with n vertices and 2m ordered pairs of adjacent vertices.  Let B be the orientation of H
from A to its complement: it is oriented, bipartite, has e arcs and a homomorphism to the arc K
(A to the tail).  Let D be the oriented bipartite double cover of G: the vertices (x,false) and
(x,true), and the arcs (x,false) -> (y,true) for the ordered pairs of adjacent vertices x, y.
It has 2n vertices and 2m arcs.  A homomorphism f from B to D is determined by its first
projection, a homomorphism from H to G, and its second projection, a map from V(H) to the two
layers; hence hom(B,D) <= 2^v hom(H,G).  The directed Sidorenko property of B in D gives
(2m)^e (2n)^v <= hom(B,D) (2n)^(2e) <= 2^v hom(H,G) 4^e n^(2e), that is Sidorenko's inequality
for H and G up to the factor 4^e.  The tensor power trick ([tensor_power.v]) removes it.

The proof is written for this repository.  The reduction was suggested by the counterexample to
Sidorenko's conjecture of OpenAI (a model-generated manuscript, not peer reviewed, whose Section 8
also uses tensor powers),
https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/preprints/A-counterexample-to-Sidorenkos-conjecture-September-23-2026/paper.pdf;
neither the paper nor OpenAI's Lean formalization contains this implication.  With that
counterexample, it would disprove the directed Sidorenko conjecture. *)

From GraphTheory Require Import digraph sgraph connectivity.
From mathcomp Require Import boot.
From GC.GraphLib Require Import homomorphism digraph.
From GC.extremal.AX_directed_sidorenko_bipartite_homomorphism Require Import tensor_power.
From GC.extremal.AX_directed_sidorenko_bipartite_homomorphism Require Import
  main(AX_directed_sidorenko_bipartite_homomorphism).
From GC.extremal.OPG_sidorenko_bipartite_homomorphism_density Require Import
  main(OPG_sidorenko_bipartite_homomorphism_density).

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Abbreviation single_arc :=
  GC.extremal.AX_directed_sidorenko_bipartite_homomorphism.main.single_arc.

(** ** The orientation of a bipartite graph *)

Section Orientation.
Variables (H : sgraph) (A : {set H}).
Hypothesis bipA : bipartition A.

(** The edges of [H], oriented from [A] to its complement. *)
Definition orientation : diGraph := DiGraph [rel x y : H | (x \in A) && (x -- y)].

Lemma edge_orientation (x y : H) : @edge_rel orientation x y = (x \in A) && (x -- y).
Proof. by []. Qed.

Lemma orientation_oriented : oriented orientation.
Proof.
by move=> x y /andP[xA xy]; apply/negP => /andP[yA _]; move: (bipA xy); rewrite xA yA.
Qed.

Lemma orientation_bipartition : @bipartition orientation A.
Proof. by move=> x y /andP[_]; apply: bipA. Qed.

Lemma orientation_homs_to_arc : homs_to orientation single_arc.
Proof. by exists (fun x => x \notin A) => x y /andP[xA /bipA] /=; rewrite xA => <-. Qed.

(** Every vertex is the tail of its arcs (in [A]) or their head. *)
Lemma num_edges_orientation : num_edges orientation = #|E(H)|.
Proof.
apply/eqP; rewrite -(eqn_pmul2l (ltn0Sn 1)) edges_sum_degrees mul2n -addnn.
rewrite -{1}(sum_outdeg orientation) -(sum_indeg orientation) -big_split /=.
apply/eqP/eq_bigr => x _; rewrite /outdeg /indeg.
have [xA|xA] := boolP (x \in A).
  have -> : #|[set u : orientation | u -- x]| = 0.
    apply: eq_card0 => u; rewrite !inE edge_orientation.
    by apply/negbTE/andP => -[uA /bipA]; rewrite uA xA.
  by rewrite addn0; apply: eq_card => y; rewrite !inE edge_orientation xA.
have -> : #|N(x : orientation)| = 0.
  by apply: eq_card0 => u; rewrite !inE edge_orientation (negbTE xA).
apply: eq_card => u; rewrite !inE edge_orientation sg_sym.
by case xu: (x -- u); rewrite ?andbF // -[u \in A]negbK -(bipA xu) xA.
Qed.

End Orientation.

(** ** The oriented bipartite double cover *)

Section DoubleCover.
Variable (G : sgraph).

(** The arcs go from [(x, false)] to [(y, true)] for the ordered pairs of adjacent [x], [y]. *)
Definition double_cover : diGraph :=
  DiGraph [rel u v : G * bool | ~~ u.2 && v.2 && (u.1 -- v.1)].

Lemma edge_double_cover (u v : G * bool) :
  @edge_rel double_cover u v = ~~ u.2 && v.2 && (u.1 -- v.1).
Proof. by []. Qed.

Lemma double_cover_oriented : oriented double_cover.
Proof. by move=> u v; rewrite !edge_double_cover => /andP[/andP[_ ->]]. Qed.

Lemma card_double_cover : #|double_cover| = 2 * #|G|.
Proof. by rewrite card_prod card_bool mulnC. Qed.

Lemma num_edges_double_cover : num_edges double_cover = num_edges G.
Proof.
pose f (p : G * G) : double_cover * double_cover := ((p.1, false), (p.2, true)).
have f_inj : injective f by move=> [? ?] [? ?] [-> ->].
rewrite /num_edges -cardsE -(card_imset _ f_inj); apply: eq_card => -[[x b] [y c]].
rewrite !inE edge_double_cover /=; apply/idP/imsetP => [/andP[/andP[]]|[[x' y'] + [-> -> -> ->]]].
  by move: b c => [] [] // _ _ xy; exists (x, y).
by rewrite inE /= => ->.
Qed.

(** A homomorphism from the orientation of [H] is a pair of a homomorphism from [H] and of a
    map to the layers. *)
Lemma hom_count_double_cover (H : sgraph) (A : {set H}) : bipartition A ->
  hom_count (orientation A) double_cover <= hom_count H G * 2 ^ #|H|.
Proof.
move=> bipA; rewrite -card_bool -card_ffun -cardsT -cardsX.
rewrite -[hom_count _ _](card_imset _ (can_inj (@ffun_splitK H G bool))).
apply: subset_leq_card; apply/subsetP => _ /imsetP[f /homsP fh ->].
rewrite in_setX in_setT andbT; apply/homsP => x y xy; rewrite !ffunE.
have [xA|xA] := boolP (x \in A).
  by move: (fh x y); rewrite edge_orientation xA xy => /(_ isT)/andP[].
have yA : y \in A by rewrite -[_ \in A]negbK -(bipA _ _ xy).
move: (fh y x); rewrite edge_orientation yA sg_sym xy edge_double_cover sg_sym.
by move=> /(_ isT)/andP[].
Qed.

End DoubleCover.

(** ** Conclusion *)

Theorem
  AX_directed_sidorenko_bipartite_homomorphism_implies_OPG_sidorenko_bipartite_homomorphism_density
  : AX_directed_sidorenko_bipartite_homomorphism -> OPG_sidorenko_bipartite_homomorphism_density.
Proof.
move=> dsid H G [A bipA] _; apply: (@tensor_power_trick _ _ _ _ (4 ^ #|E(H)|)) => {}G.
have := dsid _ (orientation_oriented bipA) (ex_intro _ A (orientation_bipartition bipA))
  (orientation_homs_to_arc bipA) _ (@double_cover_oriented G).
rewrite num_edges_orientation // num_edges_double_cover card_double_cover => h.
rewrite -(leq_pmul2l (expn_gt0 2 #|H|)) mulnCA; apply: leq_trans (leq_trans _ h) _.
  by rewrite expnMn.
apply: leq_trans (leq_mul (hom_count_double_cover G bipA) (leqnn _)) _.
by rewrite expnMn expnM [hom_count H G * _]mulnC -mulnA [hom_count H G * _]mulnCA.
Qed.

Check (AX_directed_sidorenko_bipartite_homomorphism_implies_OPG_sidorenko_bipartite_homomorphism_density :
  GC.extremal.AX_directed_sidorenko_bipartite_homomorphism.main.AX_directed_sidorenko_bipartite_homomorphism ->
  GC.extremal.OPG_sidorenko_bipartite_homomorphism_density.main.OPG_sidorenko_bipartite_homomorphism_density).
Print Assumptions
  AX_directed_sidorenko_bipartite_homomorphism_implies_OPG_sidorenko_bipartite_homomorphism_density.
