(** * The 4-cycle is not a face of any embedding in the plane

Suppose that the 4-cycle bounds a face.  Then the other face along it leaves it at each vertex:
the face that comes to the 4-cycle from a clique follows one edge of the 4-cycle, and goes to
the other clique.  So each face that meets the 4-cycle, except the 4-cycle itself, visits both
cliques.  This gives three darts of every face, except the 4-cycle, in a set [W] of 26 darts
(of 40).  So there are at most 9 faces, hence at most 8 as the Euler characteristic is even,
while an embedding in the plane has 10 faces. *)

From GraphTheory Require Import digraph sgraph.
From mathcomp Require Import boot fingroup perm.
From GC.GraphLib Require Import misc topological.
From GC.misc.AX_planar_fvs_face_packing_ratio_2 Require Import graph.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Abbreviation tail x := (sval x).1.
Local Abbreviation head x := (sval x).2.

(** An orbit that meets [A] and its complement leaves [A]. *)
Lemma porbit_exit (T : finType) (s : {perm T}) (A : pred T) x y :
  y \in porbit s x -> A x -> ~~ A y -> exists2 z, z \in porbit s x & A z && ~~ A (s z).
Proof.
case/porbitP => n ->; elim: n => [|n IH] Ax; first by rewrite expg0 perm1 Ax.
have [An|nAn] := boolP (A ((s ^+ n)%g x)); last by move=> _; exact: IH.
by rewrite expgSr permM => nA; exists ((s ^+ n)%g x); rewrite ?mem_porbit ?An.
Qed.

Section Facial.
Variables (E : embedding G12) (x0 : dart G12).
Let r := rotation E.
Let f := face_perm E.
Let O := porbit f x0.
Hypothesis inC : forall x, x \in O -> part (tail x) = 0.

Lemma fE x : f x = rev_dart (r x). Proof. exact: face_permE. Qed.

Lemma head_f x : head (f x) = tail x. Proof. exact: face_perm_head. Qed.

Lemma tail_r x : tail (r x) = tail x. Proof. exact: rotation_tail. Qed.

Lemma memf x z : (f x \in porbit f z) = (x \in porbit f z).
Proof. by rewrite porbit_sym [RHS]porbit_sym -[f x]/((f ^+ 1)%g x) porbit_perm. Qed.

Lemma memO x : (f x \in O) = (x \in O). Proof. exact: memf. Qed.

(** The face of [x0] follows the 4-cycle: around a tail [u] of one of its darts [x], the other
    darts are [r x] (the opposite of the next dart [f x]) and [r (r x)], which leaves the
    4-cycle. *)
Lemma corner x : x \in O ->
  [/\ part (head x) = 0, part (head (r x)) = 0, part (head (r (r x))) != 0, r (r (r x)) = x
    & forall z, tail z = tail x -> [\/ z = x, z = r x | z = r (r x)]].
Proof.
move=> xO; have px : part (head x) = 0.
  by have := @inC (f^-1 x)%g; rewrite -memO permKV => /(_ xO); rewrite -head_f permKV.
have prx : part (head (r x)) = 0.
  by have := inC (x := f x); rewrite memO fE => /(_ xO).
have [sz cnt] := part_cycle (inC xO).
have [] := rotation_traject E x; rewrite card_darts_at degree sz /= -/r.
move=> Ur r3 mem; split=> //; last first.
  by move=> z /eqP; rewrite -mem !inE => /or3P[] /eqP; [apply: Or31|apply: Or32|apply: Or33].
apply/eqP => prrx; suff : 2 < count (fun v => part v == 0) (nb (tail x)) by rewrite cnt.
rewrite -size_filter -[3]/(size [seq head z | z <- [:: x; r x; r (r x)]]).
apply: uniq_leq_size => [|_ /mapP[z zx ->]].
  rewrite map_inj_in_uniq // => y z; rewrite !mem => /eqP ey /eqP ez eh.
  by apply: val_inj; rewrite [LHS]surjective_pairing [RHS]surjective_pairing ey ez eh.
rewrite mem_filter nbP; move: (zx); rewrite mem => /eqP <-; rewrite (svalP z) andbT.
by move: zx; rewrite !inE => /or3P[] /eqP ->; rewrite ?px ?prx ?prrx.
Qed.

(** This face visits all vertices of the 4-cycle. *)
Lemma tail_onto u : part u = 0 -> exists2 x, x \in O & tail x = u.
Proof.
have step (v w : G12) : v -- w -> part w = 0 -> (exists2 x, x \in O & tail x = v) ->
    exists2 x, x \in O & tail x = w.
  move=> vw pw [x xO ev]; subst v; have [_ _ prrx _ cor] := corner xO.
  case: (cor (exist _ (tail x, w) vw) erefl) => ez.
  - exists (f^-1 x)%g; first by rewrite -memO permKV.
    by rewrite -head_f permKV -ez.
  - by exists (f x); [rewrite memO|rewrite fE -ez].
  - by move: prrx; rewrite -ez /= pw.
move=> pu; have := all_vertices (P := fun v => (part v == 0) ==> all (fun u => (part u == 0) ==>
  [|| u == v, u \in nb v | has (fun w => (part w == 0) && (u \in nb w)) (nb v)]) vertices)
  isT (tail x0).
have x0O : x0 \in O := porbit_id f x0.
rewrite (inC x0O) eqxx implyTb => /allP/(_ u (mem_vertices u)); rewrite pu eqxx implyTb.
have T0 : exists2 x, x \in O & tail x = tail x0 by exists x0.
case/or3P => [/eqP->//|xu|/hasP[w xw /andP[/eqP pw wu]]]; first exact: step xu pu T0.
exact: step wu pu (step _ _ xw pw T0).
Qed.

Lemma tail_corner z : part (tail z) = 0 ->
  exists2 x, x \in O & [/\ tail x = tail z & [\/ z = x, z = r x | z = r (r x)]].
Proof.
move=> /tail_onto[x xO ex]; have [_ _ _ _ cor] := corner xO.
by exists x => //; split=> //; exact: cor.
Qed.

(** Darts that leave the 4-cycle. *)
Definition out (i : nat) (y : dart G12) : bool := (part (tail y) == 0) && (part (head y) == i).

(** The other face follows two darts of the 4-cycle and leaves it for the other clique. *)
Lemma out_face i y : 0 < i -> out i y ->
  part (head (f (f y))) = 0 /\ part (tail (f (f y))) = 3 - i.
Proof.
move=> i0 /andP[/eqP py /eqP ei]; have [x xO [ex yx]] := tail_corner py.
have [px prx _ r3 _] := corner xO.
have {}yx : y = r (r x).
  by case: yx ei => // -> ei; move: i0; rewrite -ei ?px ?prx.
have x'O : (f^-1 x)%g \in O by rewrite -memO permKV.
have [_ _ out' _ _] := corner x'O; set x' := (f^-1 x)%g in x'O out'.
have fx' : f x' = x by exact: permKV.
have ffy : f (f y) = rev_dart (r (r x')).
  by rewrite [f y]fE yx r3 -fx' [f x']fE rev_dartK fE.
rewrite ffy /= tail_r tail_r; split; first exact: inC.
rewrite -ei; apply: (@part_alt (tail x) _ (tail x')) => //.
- by rewrite -[tail x']head_f fx'; exact: (svalP x).
- by rewrite ex; exact: (svalP y).
- by have := svalP (r (r x')); rewrite /= !tail_r.
- exact: inC.
- exact: inC.
- by rewrite ei -lt0n.
Qed.

(** The next dart is in this clique. *)
Lemma out_clique i y : 0 < i < 3 -> out i y ->
  part (head (f (f (f y)))) = 3 - i /\ part (tail (f (f (f y)))) != 0.
Proof.
case/andP=> i0 i3 /(out_face i0)[]; set w := f (f y) => ph pt.
rewrite head_f; split=> //; apply: contraTneq (rotation_neq E (min_degree_G12 (tail w))).
rewrite fE /= -/r => prw; rewrite negbK; apply/eqP/val_inj.
rewrite [LHS]surjective_pairing [RHS]surjective_pairing tail_r; congr pair.
apply: (@part_clique (tail w)) => //; last by rewrite pt subn_eq0 -ltnNge.
  by rewrite -{1}(tail_r w); exact: (svalP (r w)).
exact: (svalP w).
Qed.

(** A face that leaves the 4-cycle for a clique also leaves it for the other clique. *)
Lemma out_out i y : 0 < i < 3 -> out i y -> exists2 z, z \in porbit f y & out (3 - i) z.
Proof.
case/andP=> i0 i3 oy; have [_ pt] := out_face i0 oy.
have <- : porbit f (f (f y)) = porbit f y by apply/eqP; rewrite eq_porbit_mem !memf porbit_id.
have [z zy /andP[/eqP pz npz]] : exists2 z, z \in porbit f (f (f y)) &
    (part (tail z) == 3 - i) && (part (tail (f z)) != 3 - i).
  apply: (@porbit_exit _ f (fun z => part (tail z) == 3 - i) _ y); last 1 first.
  - by case/andP: oy => /eqP-> _; rewrite eq_sym subn_eq0 -ltnNge.
  - by rewrite porbit_sym !memf porbit_id.
  - by rewrite pt.
exists (f z); first by rewrite memf.
rewrite /out head_f pz eqxx andbT; apply/eqP.
have e := svalP (f z); rewrite /= head_f sg_sym in e.
by apply: part_exit e _ _; rewrite pz // subn_eq0 -ltnNge.
Qed.

(** The darts whose head is not on the 4-cycle, except those that leave it for the second
    clique: 26 darts. *)
Definition W : {set dart G12} := [set x | (part (head x) != 0) && ~~ out 2 x].

Lemma card_W : #|W| <= 26.
Proof.
pose s := [seq e <- edges | (part e.2 != 0) && ~~ ((part e.1 == 0) && (part e.2 == 2))].
rewrite -(card_imset _ val_inj); apply: leq_trans (card_size s : _ <= 26).
apply/subset_leq_card/subsetP => _ /imsetP[x xW ->]; move: xW; rewrite inE /out => xW.
rewrite mem_filter xW [val x]surjective_pairing; apply/allpairsPdep.
by exists (tail x), (head x); rewrite mem_vertices nbP (svalP x).
Qed.

(** Every other face is contained in [W] or leaves the 4-cycle for both cliques. *)
Lemma face_out z : z \notin O ->
  porbit f z \subset W \/ forall i, 0 < i < 3 -> exists2 y, y \in porbit f z & out i y.
Proof.
move=> zO; have [|/subsetPn[x xz xW]] := boolP (porbit f z \subset W); first by left.
right; have outr x2 : x2 \in O -> exists2 i, 0 < i < 3 & out i (r (r x2)).
  move=> x2O; have [_ _ prr _ _] := corner x2O; exists (part (head (r (r x2)))).
    by rewrite lt0n prr part_lt3.
  by rewrite /out !tail_r inC // !eqxx.
have [i [y [i3 yz oy]]] : exists i y, [/\ 0 < i < 3, y \in porbit f z & out i y].
  move: xW; rewrite inE negb_and !negbK => /orP[/eqP px|ox]; last by exists 2, x.
  have x'z : (f^-1 x)%g \in porbit f z by rewrite -memf permKV.
  have : part (tail (f^-1 x)%g) = 0 by rewrite -head_f permKV.
  move: (f^-1 x)%g x'z => x' x'z /tail_corner[x1 x1O [_ [] ex']].
  - case/negP: zO; have /eqP <- : porbit f x' == O by rewrite eq_porbit_mem ex'.
    by rewrite porbit_sym.
  - have fx1O : f x1 \in O by rewrite memO.
    have [i i3 oi] := outr _ fx1O; exists i, (r (r (f x1))); split=> //; rewrite -memf.
    by have [_ _ _ r3 _] := corner fx1O; rewrite [f (r _)]fE r3 [f x1]fE rev_dartK -ex'.
  - by have [i i3 oi] := outr _ x1O; exists i, (r (r x1)); rewrite -ex' in oi *.
have /eqP Ey : porbit f y == porbit f z by rewrite eq_porbit_mem.
have [y' y'z oy'] := out_out i3 oy; rewrite Ey in y'z.
move=> j j3; have [->|ij] := eqVneq j i; first by exists y.
exists y' => //; suff -> : j = 3 - i by [].
by case: i j i3 j3 ij {oy oy'} => [|[|[|]]] // [|[|[|]]].
Qed.

(** Every other face has at least three darts in [W]. *)
Lemma face_W z : z \notin O -> 2 < #|porbit f z :&: W|.
Proof.
move=> /face_out[zW|o].
  by rewrite (setIidPl zW); exact: face_size_ge3 min_degree_G12.
have [y1 y1z o1] := o 1 isT; have [y2 y2z o2] := o 2 isT.
have [h1 t1] := out_clique (isT : 0 < 1 < 3) o1; have [h2 t2] := out_clique (isT : 0 < 2 < 3) o2.
have [/eqP t0 /eqP h0] := andP o1.
have uS : uniq [:: y1; f (f (f y1)); f (f (f y2))].
  rewrite /= !inE negb_or andbT; apply/andP; split; [apply/andP; split|]; apply/eqP => e.
  - by move: h1; rewrite -e h0.
  - by move: t2; rewrite -e t0.
  - by move: h1; rewrite e h2.
rewrite cardE; apply: (uniq_leq_size uS) => x; rewrite mem_enum !inE /out.
case/or3P => /eqP->; rewrite ?memf ?y1z ?y2z ?t0 ?h0 ?h1 ?h2 //.
  by rewrite (negbTE t1).
by rewrite (negbTE t2).
Qed.

Lemma card_faces : face_count r <= 9.
Proof.
rewrite leqNgt; apply/negP => F; have := card_W; rewrite leqNgt => /negP[].
rewrite -(card_porbitsI f) (bigD1 O) ?imset_f //=; apply: leq_trans (leq_addl _ _).
apply: (@leq_trans (\sum_(X in porbits f | X != O) 3)); last first.
  apply: leq_sum => _ /andP[/imsetP[z _ ->] zO]; apply: face_W; move: zO.
  by rewrite eq_porbit_mem.
rewrite (eq_bigl (mem (porbits f :\ O))); first by move=> X; rewrite !inE andbC.
rewrite sum_nat_const; move: F; rewrite /face_count -/(face_perm E) (cardsD1 O) imset_f //.
by rewrite add1n ltnS => F; exact: (leq_mul F (leqnn 3)).
Qed.

End Facial.

(** The 4-cycle is not a face. *)
Theorem face_leaves_cycle (E : embedding G12) : planar_embedding E ->
  forall x, exists2 v, v \in face_walk E x & part v != 0.
Proof.
move=> pl x; have [/hasP//|/hasPn inC] := boolP (has (fun v => part v != 0) (face_walk E x)).
have inO y : y \in porbit (face_perm E) x -> part (sval y).1 = 0.
  move=> yx; apply/eqP; rewrite -[_ == _]negbK; apply: inC; apply: map_f.
  rewrite -fingraph.fconnect_orbit; move: yx => /porbitP[n ->]; rewrite permX.
  exact: fconnect_iter.
have := card_faces inO; rewrite leq_eqVlt => /orP[/eqP F|F].
  have := odd_face_count E (fun v => leq_trans (isT : 0 < 2) (min_degree_G12 v)).
  by rewrite F card_edges card_ord.
move: pl; rewrite /planar_embedding /embedding_genus card_edges card_ord.
move: (face_count _) F => F; do 9?[case: F => [|F] //].
Qed.
