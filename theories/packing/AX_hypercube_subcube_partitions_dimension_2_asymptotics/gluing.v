(** * Matchings of a product of hypercubes, and the lifting lemma

Q_(n+m) is the product of Q_n and Q_m.  A matching of squares of Q_(n+m) is obtained from a
matching [N z] of Q_m for each vertex z of Q_n and a matching [K x] of Q_n for each vertex x of
Q_m, if they are disjoint in the product.

Lifting lemma: let M(m) be the number of matchings of squares of Q_m.  There is a set L covered
by at least M(m) / 2^(2^m) of these matchings.  Lay four of them on the four copies of Q_m in
Q_(m+2), and cover each column x, for x not in L, by a square.  This gives f_2(m+2) different
square partitions of Q_(m+2), hence M(m)^4 <= 2^(4 2^m) f_2(m+2). *)

From GraphTheory Require Import preliminaries digraph sgraph.
From GC.packing.AX_hypercube_subcube_partitions_dimension_2_asymptotics Require Import squares.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Product.
Variables n m : nat.
Implicit Types (v : hypercube (n + m)) (z : hypercube n) (x : hypercube m).
Implicit Types (A S : {set hypercube n}) (B C : {set hypercube m}).

(** The two components of a vertex, and the vertex with given components. *)
Definition top v : hypercube n := [tuple tnth v (lshift m i) | i < n].
Definition bot v : hypercube m := [tuple tnth v (rshift n i) | i < m].
Definition join z x : hypercube (n + m) := [tuple of z ++ x].

Lemma top_join z x : top (join z x) = z.
Proof. by apply: eq_from_tnth => i; rewrite tnth_mktuple tnth_lshift. Qed.

Lemma bot_join z x : bot (join z x) = x.
Proof. by apply: eq_from_tnth => i; rewrite tnth_mktuple tnth_rshift. Qed.

Definition rect A B : {set hypercube (n + m)} := [set v | (top v \in A) && (bot v \in B)].

Lemma join_rect z x A B : (join z x \in rect A B) = (z \in A) && (x \in B).
Proof. by rewrite inE top_join bot_join. Qed.

Lemma rect_inj A B A' B' :
  A != set0 -> B != set0 -> rect A B = rect A' B' -> A = A' /\ B = B'.
Proof.
case/set0Pn=> z zA /set0Pn[x xB] eqAB.
have eqz z' x' : (z' \in A) && (x' \in B) = (z' \in A') && (x' \in B').
  by rewrite -!join_rect eqAB.
have /andP[zA' xB'] : (z \in A') && (x \in B') by rewrite -eqz zA.
split; apply/setP => y; first by have := eqz y x; rewrite xB xB' !andbT.
by have := eqz z y; rewrite zA zA'.
Qed.

Lemma rect_face z x (F : {set 'I_n}) (G : {set 'I_m}) :
  rect (face z F) (face x G) = face (join z x) (@lshift n m @: F :|: @rshift n m @: G).
Proof.
have memF i : (lshift m i \in @lshift n m @: F :|: @rshift n m @: G) = (i \in F).
  rewrite inE (mem_imset _ _ (@lshift_inj n m)) orb_idr // => /imsetP[j _ /eqP].
  by rewrite eq_lrshift.
have memG i : (rshift n i \in @lshift n m @: F :|: @rshift n m @: G) = (i \in G).
  rewrite inE (mem_imset _ _ (@rshift_inj n m)) orb_idl // => /imsetP[j _ /eqP].
  by rewrite eq_rlshift.
apply/setP => v; rewrite inE; apply/andP/faceP => [[/faceP vF /faceP vG] i|h].
  case: (split_ordP i) => j ->; rewrite ?memF ?memG => jFG.
    by rewrite tnth_lshift -vF // tnth_mktuple.
  by rewrite tnth_rshift -vG // tnth_mktuple.
split; apply/faceP => i iFG; rewrite tnth_mktuple.
  by rewrite h ?memF ?tnth_lshift.
by rewrite h ?memG ?tnth_rshift.
Qed.

Lemma face0 k (y : hypercube k) : face y set0 = [set y].
Proof.
apply/setP => y'; rewrite inE; apply/faceP/eqP => [h|-> //].
by apply: eq_from_tnth => i; rewrite h ?inE.
Qed.

Lemma row_square z C : C \in squares m -> rect [set z] C \in squares (n + m).
Proof.
move=> Csq; have [x xC] := set0Pn _ (square_neq0 Csq).
have [F F2 ->] := squareP Csq xC.
rewrite -face0 rect_face imset0 set0U face_square ?card_imset //; exact: rshift_inj.
Qed.

Lemma column_square S x : S \in squares n -> rect S [set x] \in squares (n + m).
Proof.
move=> Ssq; have [z zS] := set0Pn _ (square_neq0 Ssq).
have [F F2 ->] := squareP Ssq zS.
rewrite -face0 rect_face imset0 setU0 face_square ?card_imset //; exact: lshift_inj.
Qed.

(** ** Gluing *)

Section Glue.
Variables (N : hypercube n -> {set {set hypercube m}}).
Variables (K : hypercube m -> {set {set hypercube n}}).

Definition glue : {set {set hypercube (n + m)}} :=
  [set rect [set p.1] p.2 | p in [set p | p.2 \in N p.1]] :|:
  [set rect p.1 [set p.2] | p in [set p | p.1 \in K p.2]].

Lemma glueP Q :
  reflect ((exists z, exists2 C, C \in N z & Q = rect [set z] C) \/
           (exists x, exists2 S, S \in K x & Q = rect S [set x])) (Q \in glue).
Proof.
rewrite inE; apply: (iffP orP) => -[].
- by case/imsetP => -[z C]; rewrite inE /= => CN ->; left; exists z, C.
- by case/imsetP => -[S x]; rewrite inE /= => SK ->; right; exists x, S.
- by case=> z [C CN ->]; left; apply/imsetP; exists (z, C); rewrite ?inE.
- by case=> x [S SK ->]; right; apply/imsetP; exists (S, x); rewrite ?inE.
Qed.

Lemma card_glue : #|glue| <= \sum_z #|N z| + #|[set p | p.1 \in K p.2]|.
Proof.
have -> : \sum_z #|N z| = #|[set p | p.2 \in N p.1]|.
  by under eq_bigr do rewrite -sum1_card; rewrite pair_big_dep sum1dep_card.
by rewrite (leq_trans (leq_card_setU _ _)) // leq_add ?leq_imset_card.
Qed.

Lemma cover_glue v :
  (v \in cover glue) = (bot v \in cover (N (top v))) || (top v \in cover (K (bot v))).
Proof.
apply/bigcupP/orP => [[Q /glueP[[z [C CN ->]]|[x [S SK ->]]]]|[]/bigcupP].
- by rewrite !inE => /andP[/eqP-> vC]; left; apply/bigcupP; exists C.
- by rewrite !inE => /andP[vS /eqP->]; right; apply/bigcupP; exists S.
- case=> C CN vC; exists (rect [set top v] C); last by rewrite !inE eqxx.
  by apply/glueP; left; exists (top v), C.
- case=> S SK vS; exists (rect S [set bot v]); last by rewrite !inE eqxx andbT.
  by apply/glueP; right; exists (bot v), S.
Qed.

Hypothesis matN : forall z, N z \in matchings m.
Hypothesis matK : forall x, K x \in matchings n.
Hypothesis disjNK : forall x S z, S \in K x -> z \in S -> x \notin cover (N z).

Lemma glue_matching : glue \in matchings (n + m).
Proof.
have trivN z : trivIset (N z) by have [] := matchingP (matN z).
have trivK x : trivIset (K x) by have [] := matchingP (matK x).
apply/matchingP; split.
  apply/subsetP => Q /glueP[[z [C CN ->]]|[x [S SK ->]]].
    exact: row_square (matching_sub (matN z) CN).
  exact: column_square (matching_sub (matK x) SK).
have blockE Q v : Q \in glue -> v \in Q ->
    Q = if bot v \in cover (N (top v)) then rect [set top v] (pblock (N (top v)) (bot v))
        else rect (pblock (K (bot v)) (top v)) [set bot v].
  case/glueP => [[z [C CN ->]]|[x [S SK ->]]]; rewrite !inE.
    case/andP => /eqP-> vC; rewrite (def_pblock (trivN z) CN vC) ifT //.
    by apply/bigcupP; exists C.
  by case/andP => vS /eqP->; rewrite (negPf (disjNK SK vS)) (def_pblock (trivK x) SK vS).
apply/trivIsetP => Q Q' gQ gQ'; apply: contraR => /pred0Pn[v /andP[/= vQ vQ']].
by rewrite (blockE _ _ gQ vQ) (blockE _ _ gQ' vQ').
Qed.

Lemma glue_row z : N z = [set C in squares m | rect [set z] C \in glue].
Proof.
apply/setP => C; rewrite inE; apply/idP/andP => [CN|[Csq]].
  by split; [exact: matching_sub (matN z) CN|apply/glueP; left; exists z, C].
have inj := rect_inj (set10 z) (square_neq0 Csq).
case/glueP => [[z' [C' CN' /inj[]]]|[x [S SK /inj[_ Cx]]]]; first by move=> /set1_inj-> ->.
by have := card_square Csq; rewrite Cx cards1.
Qed.

Lemma glue_column x : K x = [set S in squares n | rect S [set x] \in glue].
Proof.
apply/setP => S; rewrite inE; apply/idP/andP => [SK|[Ssq]].
  by split; [exact: matching_sub (matK x) SK|apply/glueP; right; exists x, S].
have inj := rect_inj (square_neq0 Ssq) (set10 x).
case/glueP => [[z [C CN /inj[Sz _]]]|[x' [S' SK' /inj[]]]]; last by move=> -> /set1_inj->.
by have := card_square Ssq; rewrite Sz cards1.
Qed.

End Glue.

End Product.

(** ** Lifting *)

Theorem lifting m :
  #|matchings m| ^ 4 <= 2 ^ (4 * 2 ^ m) * square_partition_count (2 + m).
Proof.
pose A (L : {set hypercube m}) := [set M in matchings m | cover M == L].
have [L leL] : exists L, #|matchings m| <= 2 ^ 2 ^ m * #|A L|.
  have [L _ maxL] := @arg_maxnP _ set0 xpredT (fun L => #|A L|) isT; exists L.
  have <- : #|{: {set hypercube m}}| = 2 ^ 2 ^ m.
    by rewrite -cardsT -powersetT card_powerset cardsT card_hypercube.
  rewrite -sum_nat_const -sum1_card (partition_big (fun M => cover M) xpredT) //=.
  by apply: leq_sum => L' _; rewrite sum1dep_card; apply: maxL.
pose K (x : hypercube m) : {set {set hypercube 2}} := if x \in L then set0 else [set setT].
have matK x : K x \in matchings 2.
  have Ksub : K x \subset [set setT] by rewrite /K; case: ifP; rewrite ?sub0set.
  apply/matchingP; split; last exact: trivIsetS Ksub (trivIset1 _).
  rewrite (subset_trans Ksub) // sub1set.
  pose z : hypercube 2 := [tuple of nseq 2 false].
  have -> : setT = face z setT; last by rewrite face_square // cardsT card_ord.
  by apply/setP => y; rewrite inE; apply/esym/faceP => i; rewrite inE.
have famP f : f \in ffun_on (mem (A L)) ->
    forall z : hypercube 2, f z \in matchings m /\ cover (f z) = L.
  by move=> /ffun_onP fA z; have := fA z; rewrite inE => /andP[? /eqP].
have liftP f : f \in ffun_on (mem (A L)) -> glue f K \in matchings (2 + m).
  move=> /famP fA; apply: glue_matching => // [z|x S z]; first by case: (fA z).
  by case: (fA z) => _ ->; rewrite /K; case: ifP; rewrite ?inE // => /negbT.
have lift_inj : {in ffun_on (mem (A L)) &, injective (fun f : {ffun _ -> _} => glue f K)}.
  move=> f g /famP fA /famP gA eqfg; apply/ffunP => z.
  by rewrite (glue_row K (fun z => (fA z).1)) eqfg -glue_row // => z'; case: (gA z').
have : #|A L| ^ 4 <= square_partition_count (2 + m).
  rewrite -[4]/(2 ^ 2) -card_hypercube -card_ffun_on -(card_in_imset lift_inj).
  apply/subset_leq_card/subsetP => _ /imsetP[f fA ->]; rewrite inE.
  have [/subsetP sq triv] := matchingP (liftP f fA).
  apply/andP; split; last by apply/forall_inP => S /sq; rewrite inE.
  apply/and3P; split=> //; last by apply/negP => /sq/square_neq0/eqP.
  apply/eqP/setP => v; rewrite cover_glue inE; have [_ ->] := famP f fA (top v).
  by rewrite /K; case: ifP => //= _; rewrite /cover big_set1 inE.
move=> /(leq_mul (leqnn (2 ^ (4 * 2 ^ m)))); apply: leq_trans.
by rewrite [4 * _]mulnC expnM -expnMn leq_exp2r.
Qed.
