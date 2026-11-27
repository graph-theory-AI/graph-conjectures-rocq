(** * Ramsey's theorem for cliques and stable sets

A graph has an induced copy of [K_n] if and only if its clique number is at least [n].
Ramsey's theorem: the sets of vertices with no stable set of size [a + 1] and no clique of size
[s] have a bounded number of vertices. *)

From GraphTheory Require Import preliminaries digraph sgraph dom coloring.
From mathcomp Require Import boot.
From GC.GraphLib Require Import misc.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Induced copies of complete graphs *)

(** [G] has an induced copy of [K_n] if and only if it has a clique of size [n]. *)
Lemma has_induced_copy_Kn (G : sgraph) (n : nat) :
  has_induced_copy G 'K_n <-> n <= ω([set: G]).
Proof.
split=> [[i]|].
  have cl : [set: 'K_n] \in cliques [set: 'K_n].
    by rewrite inE subxx; apply/cliqueP => x y _ _.
  have := clique_bound cl; rewrite cardsT card_ord (omega_isubgraph i) => /leq_trans; apply.
  exact/sub_omega/subsetT.
case: omegaP => K /maxclique_clique clK nK.
have sKG : n <= #|induced K| by rewrite card_sig; apply: leq_trans nK _; rewrite subset_leq_card.
have wi : injective (widen_ord sKG).
  by move=> x y e; apply: val_inj; exact: (congr1 (@nat_of_ord _) e).
have j : 'K_n ⇀ 'K_#|induced K|.
  apply: (@ISubgraph 'K_n 'K_#|induced K| (widen_ord sKG) wi) => x y.
  by rewrite /edge_rel /= (inj_eq wi).
have iK : 'K_#|induced K| ≃ induced K.
  by apply/diso_sym/diso_Kn => x y xy; apply: clK; rewrite ?(valP x) ?(valP y) ?val_eqE.
exact: inhabits (isubgraph_comp j (isubgraph_comp (iso_isubgraph iK) (induced_isubgraph K))).
Qed.

(** ** Ramsey's theorem *)

(** By induction on [s] and [a]: a vertex [v] of [A] splits [A :\ v] into its neighbours, where
    the clique number is smaller, and its non-neighbours, where the independence number is
    smaller. *)
Theorem ramsey_bound (s a : nat) : exists N : nat,
  forall (G : sgraph) (A : {set G}), α(A) <= a -> ω(A) < s -> #|A| <= N.
Proof.
elim: s a => [|s IHs] a; first by exists 0.
elim: a => [|a IHa].
  by exists 0 => G A; rewrite leqn0 alpha_eq0 => /eqP-> _; rewrite cards0.
have [N1 HN1] := IHs a.+1; have [N2 HN2] := IHa.
exists (N1 + N2).+1 => G A aA oA.
have [->|/set0Pn[v vA]] := eqVneq A set0; first by rewrite cards0.
pose A1 := A :&: N(v); pose A2 := A :\: N[v].
have c1 : #|A1| <= N1.
  apply: HN1.
    case: alphaP => S /maxstabsetW /stabsetsP[SA1 stS]; apply: leq_trans aA.
    by apply/stabset_bound/stabsetsP; split=> //; apply: subset_trans SA1 (subsetIl _ _).
  case: omegaP => K; rewrite !inE => /andP[/andP[KA1 /cliqueP clK] _].
  have KN : K \subset N(v) by apply: subset_trans KA1 (subsetIr _ _).
  have vK : v \notin K by apply/negP => /(subsetP KN); rewrite in_opn sg_irrefl.
  suff : #|v |: K| <= ω(A) by rewrite cardsU1 vK add1n => h; exact: leq_ltn_trans h oA.
  apply: clique_bound; rewrite inE subUset sub1set vA (subset_trans KA1 (subsetIl _ _)).
  exact/cliqueP/cliqueU1.
have c2 : #|A2| <= N2.
  apply: HN2; last exact: leq_ltn_trans (sub_omega (subsetDl _ _)) oA.
  case: alphaP => S /maxstabsetW /stabsetsP[SA2 stS].
  have vS : v \notin S by apply/negP => /(subsetP SA2); rewrite !inE ?in_cln eqxx.
  suff : #|v |: S| <= α(A) by rewrite cardsU1 vS add1n => h; exact: leq_trans h aA.
  apply: stabset_bound; rewrite inE subUset sub1set vA (subset_trans SA2 (subsetDl _ _)) /=.
  apply/stableP => x y; rewrite !inE => /predU1P[->|xS] /predU1P[->|yS]; rewrite ?sg_irrefl //.
  - by have := subsetP SA2 y yS; rewrite !inE ?in_cln negb_or ?in_opn => /andP[/andP[_ ->]].
  - by have := subsetP SA2 x xS; rewrite !inE ?in_cln negb_or ?in_opn sg_sym => /andP[/andP[_ ->]].
  - by move/stableP: stS; apply.
have -> : A = v |: (A1 :|: A2).
  apply/setP => x; rewrite !inE ?in_cln ?in_opn.
  by case: eqVneq => [->|_]; rewrite ?vA //=; case: (x \in A); case: (v -- x).
by rewrite cardsU1; apply: leq_add (leq_b1 _) (leq_trans (leq_card_setU _ _) (leq_add c1 c2)).
Qed.
