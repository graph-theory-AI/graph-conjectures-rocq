(** * Greedy construction of a graph of large girth

A graph on n vertices is built by adding edges one by one, each from a given source.  The target is
chosen among the vertices [allowed]: those at distance at least g from the source, so that no cycle
is shorter than g, and with indegree less than 10 D.  If each vertex is the source of at most D
edges, the degrees are at most 11 D, and [allowed] contains at least 4n/5 vertices for n large
enough [card_allowed].

The targets are chosen by the method of conditional expectations.  For a set A of a <= n/2 vertices,
an edge from A has weight 4n if its target is in A, and a otherwise.  The average weight of such an
edge for all the allowed targets is at most 6a.  So some target does not increase the potential,
a sum over A of products of the weights of the edges already added, and of 6a for each edge to be
added [potential_cons].  The coefficient c(a) of A in this sum is arbitrary here. *)

From mathcomp Require Import boot zify_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Construction.
Variables D n : nat.
Implicit Types (E : seq ('I_n * 'I_n)) (s : seq 'I_n) (A : {set 'I_n}).

Lemma sum_count s : \sum_x count_mem x s = size s.
Proof.
elim: s => [|y s IH]; first by rewrite big1.
by rewrite /= big_split /= IH (bigD1 y) //= eqxx big1 // => x; rewrite eq_sym => /negPf ->.
Qed.

(** The graph with edge set [E] (a list of pairs, from source to target). *)
Definition adj E : rel 'I_n := fun x y => ((x, y) \in E) || ((y, x) \in E).

Lemma adjC E x y : adj E x y = adj E y x. Proof. exact: orbC. Qed.

(** The number of edges of source and target [x]. *)
Definition outdeg E x := count_mem x (unzip1 E).
Definition indeg E x := count_mem x (unzip2 E).

Lemma card_adj E x : #|[set y | adj E x y]| <= outdeg E x + indeg E x.
Proof.
set s := [seq e.2 | e <- E & e.1 == x] ++ [seq e.1 | e <- E & e.2 == x].
have -> : outdeg E x + indeg E x = size s.
  by rewrite size_cat !size_map !size_filter /outdeg /indeg !count_map.
apply: leq_trans (card_size s); apply/subset_leq_card/subsetP => y.
rewrite inE mem_cat => /orP[] xy; apply/orP; [left|right]; apply/mapP.
  by exists (x, y); rewrite // mem_filter eqxx.
by exists (y, x); rewrite // mem_filter eqxx.
Qed.

(** The vertices at distance at most [k] from [x], and a bound on their number when the outdegrees
    are at most [D] and the indegrees at most [10 * D]. *)
Fixpoint ball E k x : {set 'I_n} :=
  if k is k'.+1 then x |: \bigcup_(y | adj E x y) ball E k' y else [set x].

Fixpoint ball_size k := if k is k'.+1 then (11 * D * ball_size k').+1 else 1.

Lemma card_ball E k x :
  (forall y, outdeg E y <= D) -> (forall y, indeg E y <= 10 * D) -> #|ball E k x| <= ball_size k.
Proof.
move=> oE iE; elim: k x => [|k IH] x; first by rewrite /= cards1.
rewrite /= -add1n (leq_trans (leq_card_setU _ _)) // cards1 leq_add2l.
apply: leq_trans (_ : \sum_(y | adj E x y) #|ball E k y| <= _).
  elim/big_rec2: _ => [|y m B _ Bm]; first by rewrite cards0.
  by rewrite (leq_trans (leq_card_setU _ _)) // leq_add2l.
apply: leq_trans (_ : \sum_(y | adj E x y) ball_size k <= _); first by apply: leq_sum.
rewrite sum_nat_const leq_mul2r -cardsE (leq_trans (card_adj E x)) ?orbT //.
by rewrite (leq_trans (leq_add (oE x) (iE x))) // -mulSn.
Qed.

Lemma mem_ball E k x p : path (adj E) x p -> size p <= k -> last x p \in ball E k x.
Proof.
elim: k x p => [|k IH] x [|y p] //=; rewrite ?set11 ?setU11 // => /andP[xy yp] pk.
by rewrite !inE; apply/orP; right; apply/bigcupP; exists y; rewrite ?IH.
Qed.

Lemma mem_ball_sym E k x p : path (adj E) x p -> size p <= k -> x \in ball E k (last x p).
Proof.
have {2}<- : last (last x p) (rev (belast x p)) = x.
  by case: p => // y p; rewrite /= rev_cons last_rcons.
move=> xp pk; apply: mem_ball; rewrite ?size_rev ?size_belast //.
by rewrite rev_path (eq_path (e' := adj E)) // => ? ?; exact: adjC.
Qed.

(** No cycle is shorter than [g]. *)
Definition large_girth g E := forall c, ucycleb (adj E) c -> 2 < size c -> g <= size c.

(** An edge between two vertices at distance at least [g] creates no cycle shorter than [g]: such a
    cycle would contain, besides the new edge [uv], a short path from [v] to [u]. *)
Lemma large_girth_cons g E x y :
  large_girth g E -> y \notin ball E g x -> large_girth g ((x, y) :: E).
Proof.
move=> gE yx c /andP[cc uc] c2; rewrite leqNgt; apply/negP => cg.
have [cE|] := boolP (cycle (adj E) c).
  by move: cg; rewrite ltnNge gE // /ucycleb cE.
have [/allP nE|/allPn[u uc']] := boolP (all (fun u => adj E u (next c u)) c).
  by rewrite cycle_from_next.
have [i [|v p] e] := rot_to uc'; first by rewrite -(size_rot i) e in c2.
rewrite -(next_rot i uc) e /= eqxx => nuv.
move: cc uc c2 cg; rewrite -(rot_cycle i) -(rot_uniq i) -(size_rot i) e /=.
rewrite !inE negb_or => /andP[uv vp] /and3P[/andP[uNv up] vNp _] p0 pg.
have E' a b : adj ((x, y) :: E) a b ->
    [|| adj E a b, (a == x) && (b == y) | (a == y) && (b == x)].
  by rewrite /adj !inE !xpair_eqE [(b == x) && _]andbC; case: ((a, b) \in E) ((b, a) \in E);
    case; rewrite ?orbT ?orbF.
have uvxy : (u == x) && (v == y) || (u == y) && (v == x).
  by move: (E' _ _ uv); rewrite (negPf nuv).
have path_vu : path (adj E) v (rcons p u).
  move: vp; rewrite !rcons_path => /andP[vp lu]; apply/andP; split.
    apply: (@sub_in_path _ (predC1 u)) vp => [a b|].
      rewrite !inE => au bu /E' /or3P[//|/andP[/eqP ax /eqP bY]|/andP[/eqP aY /eqP bx]].
        by move: uvxy au bu; rewrite ax bY; case/orP => /andP[/eqP-> _]; rewrite eqxx.
      by move: uvxy au bu; rewrite aY bx; case/orP => /andP[/eqP-> _]; rewrite eqxx.
    by rewrite /= eq_sym uNv; apply/allP => w wp /=; apply: contraNneq up => <-.
  have lv : last v p != v.
    have : last v p \in p by case: (p) p0 => // w q _; rewrite /= mem_last.
    by apply: contraTneq => ->.
  have lNu : last v p != u.
    have := mem_last v p; rewrite inE; case/orP => [/eqP->|lp]; first by rewrite eq_sym.
    by apply: contraNneq up => <-.
  case/or3P: (E' _ _ lu) => [//|/andP[/eqP lx /eqP uy]|/andP[/eqP ly /eqP ux]].
    by move: uvxy lv uNv; rewrite lx uy eqxx /= => /orP[/andP[/eqP-> /eqP->]|/eqP->]; rewrite eqxx.
  by move: uvxy lv uNv; rewrite ly ux eqxx /= => /orP[/eqP->|/andP[/eqP-> /eqP->]]; rewrite eqxx.
have sp : size (rcons p u) <= g by rewrite size_rcons; exact: ltnW (ltnW pg).
case/orP: uvxy => /andP[/eqP ux /eqP vy].
  by case/negP: yx; rewrite -ux -vy -(last_rcons v p u) mem_ball_sym.
by case/negP: yx; rewrite -ux -vy -[X in X \in _](last_rcons v p u) mem_ball.
Qed.

(** The invariants: no short cycle, no loop, no parallel edges, bounded indegree. *)
Definition good g E :=
  [/\ large_girth g E, uniq E, forall x, ~~ adj E x x & forall y, indeg E y <= 10 * D].

(** The possible ends of a new edge from [x]. *)
Definition allowed g E x := [set y | (y \notin ball E g x) && (indeg E y < 10 * D)].

Lemma card_allowed g E x : 0 < D -> 10 * ball_size g <= n -> good g E ->
  (forall y, outdeg E y <= D) -> 4 * n <= 5 * #|allowed g E x|.
Proof.
move=> D0 ng [_ _ _ iE] oE; set full := [set y | 10 * D <= indeg E y].
have full_n : 10 * #|full| <= n.
  have : \sum_y indeg E y <= n * D.
    rewrite sum_count size_map -(size_map fst) -sum_count.
    apply: leq_trans (_ : \sum_(x < n) D <= _); last by rewrite sum_nat_const card_ord.
    by apply: leq_sum => y _; exact: oE.
  rewrite (bigID (mem full)) /= => /(leq_trans (leq_addr _ _)).
  move=> /(leq_trans _) le; rewrite mulnC -(@leq_pmul2r D) // -mulnA; apply: le.
  by rewrite -sum_nat_const leq_sum // => y; rewrite inE.
have : ~: allowed g E x \subset ball E g x :|: full.
  by apply/subsetP => y; rewrite !inE negb_and negbK -leqNgt.
move=> /subset_leq_card/leq_trans/(_ (leq_card_setU _ _)).
move=> /leq_trans/(_ (leq_add (card_ball g x oE iE) (leqnn _))).
move: (cardsC (allowed g E x)) full_n; rewrite card_ord.
by move: #|allowed g E x| #|~: _| #|full| => u v w; lia.
Qed.

Lemma good_cons g E x y : 1 < g -> good g E -> y \in allowed g E x -> good g ((x, y) :: E).
Proof.
move=> g1 [gE uE lE iE]; rewrite inE => /andP[yx iy].
have xNy : x != y.
  by apply: contraNneq yx => <-; apply: (@mem_ball E g x [::]).
have xyE : ~~ adj E x y.
  by apply: contraNN yx => xy; apply: (@mem_ball E g x [:: y]); rewrite //= ?xy // ltnW.
split; first exact: large_girth_cons.
- by rewrite /= uE andbT; apply: contraNN xyE => xy; apply/orP; left.
- move=> z; rewrite /adj orbb inE xpair_eqE negb_or; have := lE z; rewrite /adj orbb => ->.
  by rewrite andbT; apply: contraNN xNy => /andP[/eqP<-].
move=> z; rewrite /indeg /=; case: eqP => [<-|_]; [exact: iy | exact: iE].
Qed.

(** ** The potential *)

Variable c : nat -> nat.

(** The sets of at most n/2 vertices. *)
Definition small A := (0 < #|A|) && (2 * #|A| <= n).

Definition weight A (e : 'I_n * 'I_n) :=
  if e.1 \in A then if e.2 \in A then 4 * n else #|A| else 1.

(** The potential when the edges [E] have been added, with edges from [s] to be added: the average
    [weight] of an edge from [A], for all its possible targets, is at most [6 * #|A|]. *)
Definition potential E s :=
  \sum_(A | small A) c #|A| * ((6 * #|A|) ^ count (mem A) s * \prod_(e <- E) weight A e).

(** Some target does not increase the potential. *)
Lemma potential_cons E s x (Y : {set 'I_n}) : 4 * n <= 5 * #|Y| -> 0 < #|Y| ->
  exists2 y, y \in Y & potential ((x, y) :: E) s <= potential E (x :: s).
Proof.
move=> nY Y0; apply/exists_inP; apply: contraLR (leqnn (#|Y| * potential E (x :: s))).
rewrite negb_exists_in => /forall_inP gtY; rewrite -ltnNge.
apply: (@leq_trans (\sum_(y in Y) potential ((x, y) :: E) s)).
  have : \sum_(y in Y) (potential E (x :: s)).+1 <= \sum_(y in Y) potential ((x, y) :: E) s.
    by apply: leq_sum => y yY; rewrite ltnNge gtY.
  by rewrite sum_nat_const; nia.
rewrite exchange_big /= big_distrr /=; apply: leq_sum => A /andP[A0 _].
rewrite -big_distrr /= mulnCA leq_mul2l; apply/orP; right.
under eq_bigr do rewrite big_cons mulnCA; rewrite -big_distrl /=.
have wY : \sum_(y in Y) weight A (x, y) <= #|Y| * (6 * #|A|) ^ (x \in A).
  rewrite /weight /=; case: (x \in A); last by rewrite sum_nat_const.
  apply: (@leq_trans (\sum_(y in Y) ((y \in A) * (4 * n) + #|A|))).
    by apply: leq_sum => y _; case: (y \in A); rewrite ?mul1n ?leq_addr ?leq_addl.
  rewrite big_split sum_nat_const -big_distrl /= -big_mkcondr sum1_card.
  have YA : #|[pred y | (y \in Y) && (y \in A)]| <= #|A|.
    by apply/subset_leq_card/subsetP => y /andP[].
  apply: leq_trans (leq_add (leq_mul YA (leqnn _)) (leqnn _)) _.
  by rewrite expn1; move: #|Y| #|A| nY => u v; nia.
by rewrite expnD -[_ * _ * \prod_(_ <- _) _]mulnA [#|Y| * (_ * _)]mulnA leq_mul2r wY orbT.
Qed.

(** Edges can be added from all the vertices of [s] without increasing the potential. *)
Lemma extend g E s : 1 < g -> 0 < D -> 10 * ball_size g <= n -> good g E ->
  (forall x, count_mem x s + outdeg E x <= D) ->
  exists E', [/\ good g E', unzip1 E' = rev s ++ unzip1 E
                & potential E' [::] <= potential E s].
Proof.
move=> g1 D0 ng; elim: s E => [|x s IH] E gE sE; first by exists E.
have nY : 4 * n <= 5 * #|allowed g E x|.
  by apply: card_allowed => // y; apply: leq_trans (sE y); rewrite leq_addl.
have [|y yY le] := potential_cons E s x nY; first by have := ltn_ord x; lia.
have [||E' [gE' eE' leE']] := IH ((x, y) :: E); first exact: good_cons.
  by move=> z; have := sE z; rewrite /outdeg /= addnCA addnA.
exists E'; split=> //; last exact: leq_trans leE' le.
by rewrite eE' rev_cons cat_rcons.
Qed.

End Construction.
