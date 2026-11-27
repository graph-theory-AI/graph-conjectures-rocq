(** * The multicolour Erdős-Hajnal conjecture implies the Erdős-Hajnal conjecture

A graph G on n vertices is the colouring of the edges of K_n with 2 colours where adjacent pairs
have colour 1.  A set of vertices whose edges have at most one colour is then a clique or a stable
set, and a copy of the colouring of a graph H in this colouring is an induced copy of H in G.
The multicolour conjecture needs a colouring that uses both colours, that is, a graph with an edge
and a non-edge.  It is therefore applied to the disjoint union H' of H, K_2 and K_1: every graph
with no induced copy of H has no induced copy of H'.

The implication is the edge e115 of relations.json in graph-conjectures.  It was formalized in
graph-theory-rocq (extremal-graph-theory/theories/conjectures/implications_D2ram.v), with a
Ramsey bound for the graphs H that are complete or edgeless, which the disjoint union avoids. *)

From GraphTheory Require Import digraph sgraph dom coloring.
From mathcomp Require Import boot.
From GC.extremal.OPG_erdos_hajnal_multicolor_edge_coloring Require Import
  main(OPG_erdos_hajnal_multicolor_edge_coloring).
From GC.extremal.OPG_erdos_hajnal_induced_cliques Require Import
  main(OPG_erdos_hajnal_induced_cliques).

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Abbreviation uses_all_colours :=
  GC.extremal.OPG_erdos_hajnal_multicolor_edge_coloring.main.uses_all_colours.
Abbreviation contains_pattern :=
  GC.extremal.OPG_erdos_hajnal_multicolor_edge_coloring.main.contains_pattern.
Abbreviation palette_on := GC.extremal.OPG_erdos_hajnal_multicolor_edge_coloring.main.palette_on.

(** ** Graphs as colourings with 2 colours *)

Definition b2o (b : bool) : 'I_2 := Ordinal (leq_b1 b : b < 2).

Lemma b2o_inj : injective b2o.
Proof. by case=> [] [] // /(congr1 val). Qed.

(** The colouring of the edges of [K_#|G|] given by the graph [G]. *)
Definition gcol (G : sgraph) (x y : 'I_#|G|) : 'I_2 := b2o (enum_val x -- enum_val y).

Lemma gcol_sym (G : sgraph) (x y : 'I_#|G|) : gcol x y = gcol y x.
Proof. by rewrite /gcol sg_sym. Qed.

(** A copy of the colouring of [H] in that of [G] is an induced copy of [H]. *)
Lemma contains_gcol (H G : sgraph) : contains_pattern (@gcol H) (@gcol G) -> inhabited (H ⇀ G).
Proof.
case=> g [g_inj gH]; constructor.
pose f (v : H) := enum_val (g (enum_rank v)).
have f_inj : injective f by move=> x y /enum_val_inj/g_inj/enum_rank_inj.
apply: (ISubgraph f_inj) => x y; have [->|xy] := eqVneq x y; first by rewrite !sg_irrefl.
have rxy : enum_rank x != enum_rank y by rewrite (inj_eq enum_rank_inj).
by apply: b2o_inj; rewrite [LHS](gH _ _ rxy) /gcol !enum_rankK.
Qed.

(** A set of vertices of [G] whose edges have at most one colour is a clique or a stable set. *)
Lemma palette_gcol (G : sgraph) (A : {set 'I_#|G|}) :
  #|palette_on (@gcol G) A| <= 1 -> #|A| <= maxn ω([set: G]) α([set: G]).
Proof.
move=> /card_le1_eqP pal; set P := palette_on (@gcol G) A in pal *.
have one b : b2o b \notin P -> {in A &, forall x y, x != y -> enum_val x -- enum_val y = ~~ b}.
  move=> bP x y xA yA xy; apply: contraNeq bP => e; rewrite inE; apply/existsP; exists x.
  by apply/existsP; exists y; rewrite xA yA xy /gcol; case: b e; case: (_ -- _).
rewrite -(card_imset _ enum_val_inj).
have [tP|] := boolP (b2o true \in P); last move/one => st.
  have /one cl : b2o false \notin P by apply/negP => /(pal _ _ tP)/b2o_inj.
  apply/leq_trans/leq_maxl/clique_bound; rewrite inE subsetT /=.
  apply/cliqueP => _ _ /imsetP[x xA ->] /imsetP[y yA ->].
  by rewrite (inj_eq enum_val_inj) => /(cl x y xA yA) ->.
apply/leq_trans/leq_maxr/stabset_bound; rewrite inE subsetT /=.
apply/stableP => _ _ /imsetP[x xA ->] /imsetP[y yA ->].
by have [->|xy] := eqVneq x y; rewrite ?sg_irrefl ?st.
Qed.

(** ** The implication *)

Theorem OPG_erdos_hajnal_multicolor_edge_coloring_implies_OPG_erdos_hajnal_induced_cliques :
  OPG_erdos_hajnal_multicolor_edge_coloring -> OPG_erdos_hajnal_induced_cliques.
Proof.
move=> MEH H; pose H' := sjoin H (sjoin 'K_2 'K_1).
have k2 : 2 <= #|H'| by rewrite !card_sum !card_ord addnCA leq_addr.
have all : uses_all_colours (@gcol H').
  pose u : H' := inr (inl ord0); pose v : H' := inr (inl ord_max); pose w : H' := inr (inr ord0).
  case=> -[|[|//]] c; [exists (enum_rank u), (enum_rank w) | exists (enum_rank u), (enum_rank v)];
    by rewrite (inj_eq enum_rank_inj) /gcol !enum_rankK; split=> //; apply: val_inj.
have [a [b [a0 [b0 EH]]]] := MEH _ _ _ k2 (isT : 1 < 2) (@gcol_sym H') all.
exists a, (maxn a b); split=> [//|]; split=> [|G G0 free]; first exact: leq_maxl.
have [/contains_gcol[i]|[A [GA /palette_gcol AM]]] := EH _ _ (@gcol_sym G).
  by case: free; constructor; apply: isubgraph_comp i; exists inl; [apply: inl_inj|].
have M0 : 0 < maxn ω([set: G]) α([set: G]).
  by rewrite leq_max lt0n omega_eq0 -cards_eq0 cardsT -lt0n G0.
apply: leq_trans GA (leq_trans _ (leq_pexp2l M0 (leq_maxr a b))).
by rewrite leq_exp2r.
Qed.

Check (OPG_erdos_hajnal_multicolor_edge_coloring_implies_OPG_erdos_hajnal_induced_cliques :
  GC.extremal.OPG_erdos_hajnal_multicolor_edge_coloring.main.OPG_erdos_hajnal_multicolor_edge_coloring ->
  GC.extremal.OPG_erdos_hajnal_induced_cliques.main.OPG_erdos_hajnal_induced_cliques).
Print Assumptions
  OPG_erdos_hajnal_multicolor_edge_coloring_implies_OPG_erdos_hajnal_induced_cliques.
