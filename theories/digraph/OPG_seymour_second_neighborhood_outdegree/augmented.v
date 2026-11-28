(** * The augmented bipartite graph of the pruning lemma

For families [R] and [C] of pairs of vertices, the augmented graph of the paper of OpenAI
(Section 3) has left vertices R + Z and right vertices C + Z (two copies of [Z = Zset R C]); a
member of [R] is joined to the conflicting members of [C] and to the copies of the points of Z
it covers, and symmetrically.  Both sides are encoded in [(G * G) + (G * G)]: [inl] for the
original members, [inr] for the copies of Z; the relation [aug_edge] checks the memberships.

A matching splits into its original edges (between R and C), its edges alpha between R and the
right copy of Z, and its edges beta between the left copy of Z and C.  A vertex cover of size
at most |Z| + |H| made of non-isolated vertices gives the pruning (inequality (9) of the paper):
delete the original members of the cover.

Provenance: the paper "A proof of Seymour's second-neighborhood conjecture" of OpenAI, a
model-generated manuscript that is not peer reviewed,
https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/preprints/A-proof-of-Seymours-second-neighborhood-conjecture-September-23-2026/paper.pdf
and its Lean formalization (AugmentedGraph.lean, AugmentedMatching.lean, CoverPruning.lean),
https://github.com/openai/math/tree/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Combinatorics/SecondNeighborhood
which proves the full statement of the conjecture. *)

From GraphTheory Require Import digraph.
From GC.GraphLib Require Import misc konig.
From GC.digraph.OPG_seymour_second_neighborhood_outdegree Require Import defs.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** The preimage of a matching by an injective map that preserves the coordinates, possibly
    swapping them, is a matching. *)
Lemma bimatching_preim (L R L' R' : finType) (E : L -> R -> bool) (E' : L' -> R' -> bool)
    (f : L' * R' -> L * R) (M : {set L * R}) :
  bimatching E M -> injective f -> (forall e, E (f e).1 (f e).2 -> E' e.1 e.2) ->
  (forall e e', e.1 = e'.1 \/ e.2 = e'.2 -> (f e).1 = (f e').1 \/ (f e).2 = (f e').2) ->
  bimatching E' [set e | f e \in M].
Proof.
case/bimatchingP => ME M1 M2 finj fE fc; apply/bimatchingP; split.
- by move=> e; rewrite inE => /ME /fE.
- move=> e e'; rewrite !inE => eM e'M ee'; apply: finj.
  by case: (fc e e' (or_introl ee')) => [/(M1 _ _ eM e'M)|/(M2 _ _ eM e'M)].
- move=> e e'; rewrite !inE => eM e'M ee'; apply: finj.
  by case: (fc e e' (or_intror ee')) => [/(M1 _ _ eM e'M)|/(M2 _ _ eM e'M)].
Qed.

Section Augmented.
Variables (G : diGraph) (R C : {set G * G}).

Definition aug_edge (x y : (G * G) + (G * G)) : bool :=
  match x, y with
  | inl a, inl b => orig_rel R C a b
  | inl a, inr z => alpha_rel R C z a
  | inr z, inl b => beta_rel R C z b
  | inr _, inr _ => false
  end.

Implicit Types (M : {set ((G * G) + (G * G)) * ((G * G) + (G * G))}).

(** Original edges (a, b), alpha edges (z, a) and beta edges (z, b) of [M]. *)
Definition original_edges M : {set (G * G) * (G * G)} := [set e | (inl e.1, inl e.2) \in M].
Definition alpha_edges M : {set (G * G) * (G * G)} := [set e | (inl e.2, inr e.1) \in M].
Definition beta_edges M : {set (G * G) * (G * G)} := [set e | (inr e.1, inl e.2) \in M].

Lemma aug_matching_card M :
  bimatching aug_edge M -> #|M| <= #|original_edges M| + #|alpha_edges M| + #|beta_edges M|.
Proof.
case/bimatchingP => ME _ _.
have sub : M \subset [set (inl e.1, inl e.2) | e in original_edges M]
                  :|: [set (inl e.2, inr e.1) | e in alpha_edges M]
                  :|: [set (inr e.1, inl e.2) | e in beta_edges M].
  apply/subsetP => -[[a|z] [b|z']] eM; move: (ME _ eM) => //= _; rewrite !in_setU.
  - by rewrite (imset_f _ (_ : (a, b) \in _)) ?inE.
  - by rewrite (imset_f _ (_ : (z', a) \in _)) ?inE ?orbT.
  - by rewrite (imset_f _ (_ : (z, b) \in _)) ?inE ?orbT.
apply: leq_trans (subset_leq_card sub) _.
apply: leq_trans (leq_card_setU _ _) (leq_add _ (leq_imset_card _ _)).
exact: leq_trans (leq_card_setU _ _) (leq_add (leq_imset_card _ _) (leq_imset_card _ _)).
Qed.

(** The three parts are matchings of their relations, and the members matched by the original
    edges are not matched by alpha and beta. *)
Lemma aug_matching_parts M :
  bimatching aug_edge M ->
  [/\ bimatching (orig_rel R C) (original_edges M), bimatching (alpha_rel R C) (alpha_edges M),
      bimatching (beta_rel R C) (beta_edges M),
      {in original_edges M & alpha_edges M, forall e f, e.1 != f.2} &
      {in original_edges M & beta_edges M, forall e f, e.2 != f.2}].
Proof.
move=> mM; have [_ M1 M2] := bimatchingP _ _ mM.
split.
- apply: (bimatching_preim (f := fun e => (inl e.1, inl e.2)) mM) => //.
    by move=> [? ?] [? ?] [-> ->].
  by move=> e e' [->|->]; [left|right].
- apply: (bimatching_preim (f := fun e => (inl e.2, inr e.1)) mM) => //.
    by move=> [? ?] [? ?] [-> ->].
  by move=> e e' [->|->]; [right|left].
- apply: (bimatching_preim (f := fun e => (inr e.1, inl e.2)) mM) => //.
    by move=> [? ?] [? ?] [-> ->].
  by move=> e e' [->|->]; [left|right].
- move=> e f; rewrite !inE => eM fM; apply/eqP => ef.
  by move: (M1 _ _ eM fM); rewrite /= ef => /(_ erefl) [].
- move=> e f; rewrite !inE => eM fM; apply/eqP => ef.
  by move: (M2 _ _ eM fM); rewrite /= ef => /(_ erefl) [].
Qed.

(** A vertex cover of size at most |Z| + |H| made of non-isolated vertices gives the pruning
    (inequality (9) of the paper): the original members of the cover are deleted.  An initially
    conflict-free member is isolated, hence retained.  Each point of Z covered by a retained
    member has one of its copies in the cover, because its edge to that member is covered. *)
Theorem pruning_of_cover (A B : {set (G * G) + (G * G)}) :
  bivcover aug_edge A B -> #|A| + #|B| <= #|Zset R C| + #|Hset R C| ->
  {in A, forall x, [exists y, aug_edge x y]} -> {in B, forall y, [exists x, aug_edge x y]} ->
  pruning_result R C (R :\: [set a | inl a \in A]) (C :\: [set b | inl b \in B]).
Proof.
move=> cov AB Ane Bne.
have {}cov x y : aug_edge x y -> (x \in A) || (y \in B).
  by move/forallP: cov => /(_ x) /forallP /(_ y) /implyP.
set R' := R :\: _; set C' := C :\: _.
have inR' a : (a \in R') = (inl a \notin A) && (a \in R) by rewrite !inE.
have inC' b : (b \in C') = (inl b \notin B) && (b \in C) by rewrite !inE.
split.
- by rewrite !subsetDl.
- apply/conflict_freeP => a b; rewrite inR' inC' => /andP [aA aR] /andP [bB bC].
  apply/negP => ab; have := cov (inl a) (inl b).
  by rewrite /= /orig_rel aR bC ab (negbTE aA) (negbTE bB) => /(_ isT).
- (* a member covering a point of Z conflicts with the member witnessing it *)
  move=> a aR /forall_inP nc; rewrite inR' aR andbT; apply/negP => /Ane /existsP [[b|z]].
    by rewrite /= /orig_rel aR => /and3P [_ /nc /negP].
  rewrite /= /alpha_rel => /and3P [/setIP [_]].
  rewrite in_right_image => /existsP [s /andP [sC sz]] _ /andP [/eqP az pz].
  by have := nc _ sC; rewrite /conflict /= az pz sz.
- move=> b bC /forall_inP nc; rewrite inC' bC andbT; apply/negP => /Bne /existsP [[a|z]].
    by rewrite /= /orig_rel bC => /and3P [/nc /negP].
  rewrite /= /beta_rel => /and3P [/setIP [+ _]].
  rewrite in_left_image => /existsP [p /andP [pR pz]] _ /andP [/eqP bz sz].
  by have := nc _ pR; rewrite /conflict /= bz pz sz.
(* the charge: the covered points of Z have a copy in the cover *)
pose AZ := [set z | inr z \in A]; pose BZ := [set z | inr z \in B].
have charge : #|Zset R C :&: (left_image R' :|: right_image C')| <= #|AZ| + #|BZ|.
  rewrite addnC; apply: leq_trans (leq_card_setU _ _); apply/subset_leq_card/subsetP => z.
  rewrite in_setI in_setU in_left_image in_right_image.
  move=> /andP [zZ /orP [/existsP [p /andP [pR pz]]|/existsP [s /andP [sC sz]]]]; rewrite !inE.
    move: pR; rewrite inR' => /andP [pA pR].
    have := cov (inl (p, z.2)) (inr z); rewrite /= /alpha_rel zZ pR /lcovers eqxx pz.
    by rewrite (negbTE pA) => /(_ isT) /= ->.
  move: sC; rewrite inC' => /andP [sB sC].
  have := cov (inr z) (inl (z.1, s)); rewrite /= /beta_rel zZ sC /rcovers eqxx sz.
  by rewrite (negbTE sB) orbF => /(_ isT) ->; rewrite orbT.
have del (T : {set G * G}) (D : {set (G * G) + (G * G)}) :
    #|T :\: (T :\: [set a | inl a \in D])| <= #|[set a | inl a \in D]|.
  apply/subset_leq_card/subsetP => a.
  by rewrite !inE negb_and negbK => /andP [/orP [] // /negP].
rewrite -(leq_add2r #|Zset R C :&: (left_image R' :|: right_image C')|).
rewrite -[X in _ <= X]addnA [X in _ <= _ + X]addnC cardsID [X in _ <= X]addnC.
apply: leq_trans AB; rewrite (card_sum_set A) (card_sum_set B) addnACA.
exact: leq_add (leq_add (del _ _) (del _ _)) charge.
Qed.

End Augmented.
