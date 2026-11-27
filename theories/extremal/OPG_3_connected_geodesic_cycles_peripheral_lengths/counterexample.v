(** * A counterexample: the triakis tetrahedron

For each assignment of positive lengths to the edges of TT, some geodesic cycle is not peripheral.
Suppose on the contrary that all geodesic cycles are peripheral, hence are faces of TT, that is
triangles [s i; b j; b k].  Call an edge of the K4 tight if it is a shortest walk.  No triangle of
the K4 is geodesic, so each of them has an edge which is not tight, and hence the K4 has two edges
which are not tight, e and e'.  Let A (resp. A') be a face containing e (resp. e'); among the two
such faces, we choose the one with the larger total length of the other two edges.

Let D be the set of the edges crossed by a curve from A to A' on the sphere.  The faces with an odd
number of edges in D are A and A'.  A lightest closed walk among those with an odd number of edges
in D is a geodesic cycle (file lightest.v), hence it is A or A', say A = [s p; b j; b k].  As the
edge b j -- b k is not tight, the lighter arc of A from b j to b k is the path through s p.  Let
[s q; b j; b k] be the other face containing this edge.  By the choice of A, the path from b j to
b k through s q is also lighter than the edge.  Then [s p; b j; s q; b k] is a lighter closed walk
than A, with an odd number of edges in D: a contradiction.

The counterexample comes from Graph-Theory-LLM-Proofs
(attacks_opg/geodesic_cycles_and_tuttes_theorem).  It was formalized in graph-theory-rocq
(extremal-graph-theory/theories/applications); the proof given here is simpler. *)

From GraphTheory Require Import preliminaries digraph sgraph connectivity.
From GC.GraphLib Require Import misc.
From GC.extremal.OPG_3_connected_geodesic_cycles_peripheral_lengths Require main.
From GC.extremal.OPG_3_connected_geodesic_cycles_peripheral_lengths Require Import lightest.
From GC.extremal.OPG_3_connected_geodesic_cycles_peripheral_lengths Require Import
  triakis_tetrahedron.
From mathcomp Require Import boot order ssralg ssrnum rat.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.Theory GRing.Theory Num.Theory.

(** ** Indices *)

Lemma ord4_all (p q j k t : 'I_4) : uniq [:: p; q; j; k] -> t \in [:: p; q; j; k].
Proof. by move=> u; apply: ord_size_enum. Qed.

Lemma two_fresh (j k : 'I_4) : j != k -> exists p q, uniq [:: p; q; j; k].
Proof.
move=> jk; have [q qN] := @ord_fresh 4 [:: j; k] isT.
have [p pN] := @ord_fresh 4 [:: q; j; k] isT.
by exists p, q; rewrite !cons_uniq pN qN inE jk.
Qed.

(** A pair of indices is determined by the other two. *)
Lemma two_left (p q j k j' k' : 'I_4) : uniq [:: p; q; j; k] -> uniq [:: p; q; j'; k'] ->
  (j' = j /\ k' = k) \/ (j' = k /\ k' = j).
Proof.
move=> u; have := (ord4_all j' u, ord4_all k' u); rewrite !inE => -[].
by case/or4P=> /eqP-> /or4P[] /eqP->; rewrite /= !inE ?eqxx ?orbT ?andbF //; auto.
Qed.

Lemma other_two (p q j k t : 'I_4) :
  uniq [:: p; q; j; k] -> t \notin [:: j; k] -> t \in [:: p; q].
Proof. by move/(ord4_all t); rewrite -(cat_cons p [:: q]) mem_cat => /orP[//|->]. Qed.

Lemma uniq4E (p q j k : 'I_4) :
  uniq [:: p; q; j; k] = [&& p != q, q \notin [:: j; k] & uniq [:: p; j; k]].
Proof. by rewrite /= !inE; do ?case: (_ == _). Qed.

(** ** Faces and curves *)

(** The face [(i, m)] is the triangle [s i; b j; b k], where [{i, m, j, k}] is the set of all
    indices.  A curve from the face [(p, q)] to the face [(p', q')]: it goes around [s p] to the
    face [(p, p')], crosses the edge of the K4 without end in [b p, b p'], and goes around [s p'].
    This relation represents the set of the edges which it crosses (an odd number of times). *)
Definition curve (p q p' q' : 'I_4) : rel TT := fun x y =>
  match x, y with
  | (true, i), (false, t) | (false, t), (true, i) =>
      ((i == p) && ((t == q) (+) (t == p'))) (+) ((i == p') && ((t == q') (+) (t == p)))
  | (false, t), (false, u) => [&& p != p', t \notin [:: p; p'] & u \notin [:: p; p']]
  | (true, _), (true, _) => false
  end.

Lemma curve_sym p q p' q' : symmetric (curve p q p' q').
Proof. by move=> [[] i] [[] j] //=; rewrite [(j \notin _) && _]andbC. Qed.

(** The set of the edges which belong to a relation. *)
Definition edges_of (r : rel TT) : pred {set TT} :=
  fun e => [exists x, exists y, (e == [set x; y]) && r x y].

Lemma edges_ofE (r : rel TT) x y : symmetric r -> edges_of r [set x; y] = r x y.
Proof.
move=> r_sym; apply/existsP/idP => [[u /existsP[v /andP[/eqP e]]]|rxy].
  by case/doubleton_eq_iff: e => -[<- <-]; rewrite // r_sym.
by exists x; apply/existsP; exists y; rewrite eqxx.
Qed.

Lemma cycle_sum3 (V : nmodType) (f : {set TT} -> V) x y z :
  cycle_sum f [:: x; y; z] = (f [set x; y] + (f [set y; z] + f [set x; z]))%R.
Proof. by rewrite /cycle_sum /seq_cycle_edge_list /= !big_cons big_nil addr0 (setUC [set z]). Qed.

Lemma cycle_sum4 (V : nmodType) (f : {set TT} -> V) x y z t :
  cycle_sum f [:: x; y; z; t] =
  (f [set x; y] + (f [set z; y] + f [set z; t] + f [set x; t]))%R.
Proof.
rewrite /cycle_sum /seq_cycle_edge_list /= !big_cons big_nil addr0 !addrA.
by rewrite (setUC [set y]) (setUC [set t]).
Qed.

(** The faces with an odd number of edges crossed by the curve are its ends. *)
Lemma odd_face p q p' q' i j k :
  p != q -> p' != q' -> uniq [:: i; j; k] ->
  odd_walk (edges_of (curve p q p' q')) [:: s i; b j; b k] =
  ((i == p) && (q \notin [:: j; k])) (+) ((i == p') && (q' \notin [:: j; k])).
Proof.
move=> pq pq' u; rewrite /odd_walk cycle_sum3 !oddD !oddb !edges_ofE; try exact: curve_sym.
move: (u); rewrite /= !inE !negb_or andbT => /andP[/andP[ij ik] jk].
have jkN t : ~~ ((j == t) && (k == t)) by apply: contraNN jk => /andP[/eqP-> /eqP->].
rewrite !(eq_sym q) !(eq_sym q'); rewrite !(eq_sym i) in ij ik.
have [ei|ip] := eqVneq i p; have [ei'|ip'] := eqVneq i p'; last 1 first.
- rewrite /= addbF; apply/negP => /and3P[pp' /andP[jp jp'] /andP[kp kp']].
  have u4 : uniq [:: p; i; j; k] by rewrite cons_uniq u !inE !negb_or !(eq_sym p) jp kp ip.
  have := ord4_all p' u4; rewrite !inE !(eq_sym p') (negPf ip') (negPf jp') (negPf kp').
  by rewrite (negPf pp').
all: rewrite -?ei -?ei' ?ip' ?(eq_sym p) ?ip ?eqxx ?(negPf ij) ?(negPf ik) /=.
all: move: (jkN p) (jkN q) (jkN p') (jkN q').
all: by do ?case: (_ == _).
Qed.

(** Two faces sharing the edge [b j -- b k]. *)
Lemma odd_walk4 D i i' j k : odd_walk D [:: s i; b j; s i'; b k] =
  odd_walk D [:: s i; b j; b k] (+) odd_walk D [:: s i'; b j; b k].
Proof.
rewrite /odd_walk cycle_sum4 !cycle_sum3 !oddD.
by case: (odd _); case: (odd _); case: (odd _); case: (odd _); case: (odd _).
Qed.

(** ** The proof *)

Section Lengths.
Variables (R : realFieldType) (ell : {set TT} -> R).
Hypothesis ell_gt0 : forall e, e \in E(TT) -> (0 < ell e)%R.
Hypothesis geo_peri : forall c, geodesic_cycle ell c -> peripheral_cycle c.

(** The edge [b j -- b k] is a shortest walk. *)
Definition tight (j k : 'I_4) : Prop := shortest_walk ell (b j) (b k) [:: b k].

(** The length of the path from [b j] to [b k] through [s i]. *)
Definition len2 (i j k : 'I_4) : R := (ell [set s i; b j] + ell [set s i; b k])%R.

(** The face [(p, q)] contains an edge of the K4 which is not tight, and among the two faces
    containing this edge, the sum of the lengths of the other two edges is the larger for
    [(p, q)]. *)
Definition long_face (p q : 'I_4) : Prop :=
  exists j k, [/\ uniq [:: p; q; j; k], ~ tight j k & (len2 q j k <= len2 p j k)%R].

Lemma tight_sym j k : tight j k -> tight k j.
Proof. exact: (shortest_walk_rev (p := [::])). Qed.

Lemma tight_dn j k : j != k -> ~ ~ tight j k -> tight j k.
Proof.
move=> jk nn; split=> // [|q pq lq]; first by rewrite /= ttE /= jk.
case: leP => // lt; case: nn => -[_ _ /(_ q pq lq)].
by rewrite leNgt lt.
Qed.

Lemma long_face_exists j k : j != k -> ~ tight j k ->
  exists p q, uniq [:: p; q; j; k] /\ long_face p q.
Proof.
move=> jk nt; have [p [q u]] := two_fresh jk.
have u' : uniq [:: q; p; j; k] by rewrite (perm_uniq (permEl (perm_catCA [:: q] [:: p] _))).
have [le_qp|/ltW le_pq] := leP (len2 q j k) (len2 p j k).
  by exists p, q; split=> //; exists j, k.
by exists q, p; split=> //; exists j, k.
Qed.

(** A triangle of the K4 has an edge which is not tight. *)
Lemma triangle_not_tight i :
  ~ (forall j k, i \notin [:: j; k] -> j != k -> tight j k).
Proof.
move=> all_tight; have [j] := @ord_fresh 4 [:: i] isT; rewrite mem_seq1 => ji.
have [k [l u]] := two_fresh ji.
apply: (@K4_not_peripheral k l j); last apply: geo_peri.
  by move: u; rewrite -[[:: k; l; j; i]]/([:: k; l; j] ++ [:: i]) cat_uniq => /andP[].
move: u; rewrite /= !inE !negb_or !andbT => /and3P[/and3P[kl kj ki] /andP[lj li] _]; split.
  rewrite /main.seq_cycle /ucycleb /= !ttE !inE !negb_or !xpair_eqE /= !andbT.
  by rewrite kl kj lj eq_sym kj.
move=> x y; rewrite !inE => xC yC; have [<-|xy] := eqVneq x y.
  by exists [::]; split=> //; apply: shortest_walk_nil.
exists [:: y]; split=> [|e].
  by case/or3P: xC xy => /eqP->; case/or3P: yC => /eqP->; rewrite ?eqxx // => _;
    apply: all_tight; rewrite ?inE ?negb_or ?(eq_sym i) ?ki ?li ?ji // eq_sym.
rewrite inE => /eqP-> /=; rewrite !inE.
by case/or3P: xC xy => /eqP->; case/or3P: yC => /eqP->; rewrite ?eqxx // => _;
  rewrite ?eqxx ?orbT // setUC eqxx ?orbT.
Qed.

(** A lightest odd closed walk is not a long face if the other face containing the edge which is
    not tight is even. *)
Lemma long_face_not_lightest D p q j k : uniq [:: p; q; j; k] -> long_face p q ->
  lightest_odd ell D [:: s p; b j; b k] -> ~~ odd_walk D [:: s q; b j; b k] -> False.
Proof.
move=> u [j' [k' [u' nt le_qp]]] lc oq.
have {nt le_qp u'} [nt le_qp] : ~ tight j k /\ (len2 q j k <= len2 p j k)%R.
  have [[-> ->]|[-> ->]] := two_left u' u; first by [].
  by rewrite /len2 [leLHS]addrC [leRHS]addrC; split=> // /tight_sym.
have arc := lighter_arc (s := [::]) (t := [:: s p]) (lightest_odd_rot 1 lc).
rewrite walk_sum1 walk_sum2 in arc.
case: lc => _ op le_c; have := le_c [:: s p; b j; s q; b k].
rewrite odd_walk4 op (negPf oq) cycle_sum3 cycle_sum4 lerD2l lerD2r => /(_ _ isT) le_jk.
case: nt; apply: arc; apply: le_trans (le_jk _) _.
  move: u; rewrite /= !inE !negb_or => /and3P[/and3P[_ pj pk] /andP[qj qk] _].
  by rewrite !ttE /= !andbT pj qk eq_sym qj eq_sym pk.
by apply: le_trans le_qp _; rewrite /len2 addrC (setUC [set s p] [set b k]).
Qed.

Lemma long_faces p q p' q' : long_face p q -> long_face p' q' ->
  ~~ ((p' \in [:: p; q]) && (q' \in [:: p; q])) -> False.
Proof.
move=> lf lf' N; have [j [k [u _ _]]] := lf; have [j' [k' [u' _ _]]] := lf'.
move: (u) (u'); rewrite 2!uniq4E => /and3P[pq qN u3] /and3P[pq' _ _] {u'}.
pose D := edges_of (curve p q p' q').
have [||c lc] := @lightest_odd_exists _ _ _ ell_gt0 D [:: s p; b j; b k].
- move: u; rewrite /= !inE !negb_or => /and3P[/and3P[_ pj pk] _ /andP[jk _]].
  by rewrite !ttE /= !andbT pj jk eq_sym.
- rewrite odd_face // eqxx qN; apply/negP => /andP[/eqP ep /(other_two u) q'pq].
  by rewrite q'pq -ep mem_head in N.
have [n [x [j1 [k1 e]]]] : exists n x j k, rot n c = [:: x; b j; b k].
  exact/tt_induced_cycle/(geo_peri (lightest_odd_geodesic ell_gt0 lc)).1.
have := lightest_odd_rot n lc; rewrite e => {e c n}lc.
have {}u : uniq [:: x.2; j1; k1].
  case: lc => /andP[/and4P[]]; rewrite !ttE /= => /andP[xj _] /andP[jk _] /andP[kx _] _ _ _ _.
  by rewrite !inE negb_or xj jk eq_sym kx.
case: x u lc => [[] i] u lc; last first.
  exact: K4_not_peripheral u (geo_peri (lightest_odd_geodesic ell_gt0 lc)).
have [_ oc _] := lc; rewrite odd_face // in oc.
have [/andP[/eqP ei q1]|F] := boolP ((i == p) && (q \notin [:: j1; k1])).
  have u1 : uniq [:: p; q; j1; k1] by rewrite uniq4E pq q1 -ei u.
  rewrite ei in lc; apply: (long_face_not_lightest u1 lf lc).
  have u2 : uniq [:: q; j1; k1] by case/andP: u1.
  rewrite odd_face // eq_sym (negPf pq) /=; apply/negP => /andP[/eqP ep /(other_two u1) q'pq].
  by rewrite q'pq -ep !inE eqxx orbT in N.
rewrite (negPf F) /= in oc; case/andP: oc => /eqP ei q1.
have u1 : uniq [:: p'; q'; j1; k1] by rewrite uniq4E pq' q1 -ei u.
rewrite ei in lc; apply: (long_face_not_lightest u1 lf' lc).
have u2 : uniq [:: q'; j1; k1] by case/andP: u1.
rewrite odd_face // [q' == p']eq_sym (negPf pq') addbF; apply/negP => /andP[/eqP ep].
move/(other_two u1); rewrite !inE ep eq_sym [q == p]eq_sym (negPf pq) orbF => /eqP ep'.
by rewrite ep ep' !inE !eqxx !orbT in N.
Qed.

Lemma not_geo_peri : False.
Proof.
apply: (@triangle_not_tight ord0) => j k jN jk; apply: tight_dn => // nt.
have [p [q [u lf]]] := long_face_exists jk nt.
apply: (@triangle_not_tight j) => j' k' jN' jk'; apply: tight_dn => // nt'.
have [p' [q' [u' lf']]] := long_face_exists jk' nt'.
apply: (long_faces lf lf'); apply/negP => /andP[p'pq q'pq].
have : j \in [:: p; q] by have := other_two u' jN'; rewrite inE mem_seq1 => /orP[]/eqP->.
have : uniq ([:: p; q] ++ [:: j; k]) by [].
by rewrite cat_uniq /= negb_or !inE => /and3P[_ /andP[/negPf->]].
Qed.

End Lengths.

Lemma counterexample : ~ main.OPG_3_connected_geodesic_cycles_peripheral_lengths.
Proof. by case/(_ rat TT tt_3connected) => ell [pos geo]; apply: not_geo_peri pos geo. Qed.
