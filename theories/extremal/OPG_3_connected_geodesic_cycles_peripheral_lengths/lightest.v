(** * A lightest odd closed walk is a geodesic cycle

The edges of a graph have positive lengths, and D is a set of edges.  Call a closed walk odd if it
has an odd number of edges in D.  If there is an odd closed walk, then there is a lightest one which
is a cycle, and it is geodesic: for any two of its vertices, the lighter of the two arcs between
them is a shortest walk. *)

From GraphTheory Require Import digraph sgraph connectivity.
From GC.GraphLib Require Import misc.
From GC.extremal.OPG_3_connected_geodesic_cycles_peripheral_lengths Require main.
From mathcomp Require Import boot order ssralg ssrnum.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.Theory GRing.Theory Num.Theory.

Abbreviation shortest_walk := main.shortest_walk.
Abbreviation geodesic_cycle := main.geodesic_cycle.

Section Walks.
Variable G : sgraph.
Implicit Types (u v : G) (p q s t c : seq G).

(** A closed walk visiting [u] and [v] is a walk from [u] to [v] and a walk from [v] to [u]. *)
Lemma cycle_cat2 u s v t :
  cycle (--) (u :: s ++ v :: t) = path (--) u (rcons s v) && path (--) v (rcons t u).
Proof. by rewrite /= rcons_cat rcons_cons -cat_rcons cat_path last_rcons. Qed.

Lemma path_rev u p v :
  path (--) u (rcons p v) -> path (--) v (rcons (rev p) u).
Proof.
move=> pp; rewrite -[path _ _ _]/(sorted (--) (v :: rcons (rev p) u)).
rewrite -rev_cons -rev_rcons rev_sorted.
by rewrite (eq_sorted (e' := (--))) // => x y; rewrite sg_sym.
Qed.

(** A sequence with a repeated element has a rotation of the form [x :: s ++ x :: t]. *)
Lemma not_uniq_rot c : ~~ uniq c -> exists n x s t, rot n c = x :: s ++ x :: t.
Proof.
suff split : ~~ uniq c -> exists x s1 s2 s3, c = s1 ++ x :: s2 ++ x :: s3.
  case/split=> x [s1 [s2 [s3 ->]]]; exists (size s1), x, s2, (s3 ++ s1).
  by rewrite rot_size_cat cat_cons -catA.
elim: c => //= x c IHc; rewrite negb_and negbK => /orP[/splitPr[s t]|/IHc[y [s1 [s2 [s3 ->]]]]].
  by exists x, [::], s, t.
by exists y, (x :: s1), s2, s3.
Qed.

End Walks.

(** ** Lengths *)

Section Sums.
Variables (G : sgraph) (V : nmodType) (f : {set G} -> V).
Implicit Types (u v : G) (p s t c : seq G).

Open Scope ring_scope.

(** The sum of [f] over the edges of a walk. *)
Definition walk_sum u p : V := \sum_(e <- seq_edge_list (u :: p)) f e.

(** The sum of [f] over the edges of a closed walk. *)
Definition cycle_sum c : V := \sum_(e <- seq_cycle_edge_list c) f e.

Lemma walk_sum_cons u v p : walk_sum u (v :: p) = f [set u; v] + walk_sum v p.
Proof. by rewrite /walk_sum seq_edge_list_cons big_cons. Qed.

Lemma walk_sum1 u v : walk_sum u [:: v] = f [set u; v].
Proof. by rewrite /walk_sum big_seq1. Qed.

Lemma walk_sum2 u v w : walk_sum u [:: v; w] = f [set u; v] + f [set v; w].
Proof. by rewrite walk_sum_cons walk_sum1. Qed.

Lemma walk_sum_rev u p v : walk_sum v (rcons (rev p) u) = walk_sum u (rcons p v).
Proof.
by rewrite /walk_sum -rev_cons -rev_rcons rcons_cons seq_edge_list_rev big_rev.
Qed.

Lemma cycle_sum_cat2 u s v t :
  cycle_sum (u :: s ++ v :: t) = walk_sum u (rcons s v) + walk_sum v (rcons t u).
Proof.
by rewrite /cycle_sum seq_cycle_edge_list_cat big_cat.
Qed.

Lemma cycle_sum_rot n c : cycle_sum (rot n c) = cycle_sum c.
Proof. exact/perm_big/perm_seq_cycle_edge_list_rot. Qed.

End Sums.

Section Lightest.
Variables (R : realFieldType) (G : sgraph) (ell : {set G} -> R).
Hypothesis ell_gt0 : forall e, e \in E(G) -> (0 < ell e)%R.
Implicit Types (u v : G) (p q s t c : seq G).

Lemma walk_sum_ge0 u p : path (--) u p -> (0 <= walk_sum ell u p)%R.
Proof.
elim: p u => [|v p IHp] u /=; first by rewrite /walk_sum big_nil.
by case/andP=> uv /IHp; rewrite walk_sum_cons; apply: addr_ge0; rewrite ltW ?ell_gt0 ?in_edges.
Qed.

Lemma cycle_sum_ge0 c : cycle (--) c -> (0 <= cycle_sum ell c)%R.
Proof.
case: c => [|u s]; first by rewrite /cycle_sum big_nil.
by rewrite /cycle_sum seq_cycle_edge_list_cons; apply: walk_sum_ge0.
Qed.

Lemma shortest_walk_nil u : shortest_walk ell u u [::].
Proof. by split=> // q pq _; rewrite /main.walk_weight big_nil walk_sum_ge0. Qed.

Lemma shortest_walk_rev u p v :
  shortest_walk ell u v (rcons p v) -> shortest_walk ell v u (rcons (rev p) u).
Proof.
case=> pp _ le_p; split; rewrite ?last_rcons ?path_rev // => q.
rewrite -[leLHS]/(walk_sum ell v _) walk_sum_rev -[leRHS]/(walk_sum ell v q).
case/lastP: q => [_ /= e|q w pq]; first by subst v; apply: (le_p [::]).
rewrite last_rcons => e; subst w; rewrite -[leRHS]walk_sum_rev.
by apply: le_p; rewrite ?last_rcons ?path_rev.
Qed.

Variable D : pred {set G}.

(** The parity of the number of edges of a closed walk which are in [D]. *)
Definition odd_walk c : bool := odd (cycle_sum (fun e => D e : nat) c).

(** [c] is a lightest closed walk among those with an odd number of edges in [D], and it is a
    cycle. *)
Definition lightest_odd c : Prop :=
  [/\ ucycle (--) c, odd_walk c &
      forall d, cycle (--) d -> odd_walk d -> (cycle_sum ell c <= cycle_sum ell d)%R].

Lemma lightest_odd_rot n c : lightest_odd c -> lightest_odd (rot n c).
Proof.
case=> uc oc le_c; split; first by rewrite rot_ucycle.
  by rewrite /odd_walk cycle_sum_rot.
by rewrite cycle_sum_rot.
Qed.

(** An odd closed walk can be shortened to an odd cycle. *)
Lemma odd_cycle c : cycle (--) c -> odd_walk c ->
  exists d, [/\ ucycle (--) d, odd_walk d & (cycle_sum ell d <= cycle_sum ell c)%R].
Proof.
have [n] := ubnP (size c); elim: n c => // n IHn c lt_c cc oc.
have [uc|/not_uniq_rot[k [x [s [t ek]]]]] := boolP (uniq c).
  by exists c; rewrite /ucycle cc uc.
have := lt_c; rewrite -(size_rot k) ek /= size_cat addnS ltnS => lt_st.
have e (V : nmodType) (f : {set G} -> V) :
    cycle_sum f c = (cycle_sum f (x :: s) + cycle_sum f (x :: t))%R.
  by rewrite -(cycle_sum_rot _ k) ek cycle_sum_cat2 /cycle_sum !seq_cycle_edge_list_cons.
move: cc; rewrite -(rot_cycle k) ek cycle_cat2 => /andP[cs ct].
have : odd_walk (x :: s) || odd_walk (x :: t).
  by move: oc; rewrite /odd_walk e oddD; case: (odd _).
case/orP=> [/(IHn (x :: s) _ cs)|/(IHn (x :: t) _ ct)] [|d [ud od le_d]].
- by apply: leq_trans lt_st; rewrite !ltnS leq_addr.
- by exists d; split=> //; apply: le_trans le_d _; rewrite e lerDl cycle_sum_ge0.
- by apply: leq_trans lt_st; rewrite !ltnS leq_addl.
- by exists d; split=> //; apply: le_trans le_d _; rewrite e lerDr cycle_sum_ge0.
Qed.

Lemma lightest_odd_exists c : cycle (--) c -> odd_walk c -> exists d, lightest_odd d.
Proof.
move=> cc oc; have [d0 [ud0 od0 _]] := odd_cycle cc oc.
have size_d (d : seq G) : ucycle (--) d -> size d <= #|G|.
  by case/andP=> _ /card_uniqP <-; apply: max_card.
pose P (d : #|G|.-bseq G) := ucycleb (--) d && odd_walk d.
have P0 : P (Bseq (size_d _ ud0)) by apply/andP.
case: (Order.TotalTheory.arg_minP (fun d : #|G|.-bseq G => cycle_sum ell d) P0).
move=> d /andP[ud od] le_d; exists d; split=> // e ce oe.
have [e' [ue' oe' le_e']] := odd_cycle ce oe.
by apply: le_trans le_e'; apply: (le_d (Bseq (size_d _ ue'))); apply/andP.
Qed.

(** Two vertices cut a lightest odd cycle in two arcs, and the lighter arc is a shortest walk: a
    lighter walk would form with each arc a closed walk lighter than the cycle, and one of these
    two closed walks would be odd. *)
Lemma lighter_arc u s v t : lightest_odd (u :: s ++ v :: t) ->
  (walk_sum ell u (rcons s v) <= walk_sum ell v (rcons t u))%R ->
  shortest_walk ell u v (rcons s v).
Proof.
case=> /andP[]; rewrite cycle_cat2 => /andP[ps pt] uc oc le_c le_st.
split; rewrite ?last_rcons // => q pq lq.
rewrite -[main.walk_weight _ _ _]/(walk_sum _ _ _) -[leRHS]/(walk_sum _ _ _).
case/lastP: q pq lq => [_ /= uv|q w pq].
  by move: uc; rewrite uv /= mem_cat mem_head orbT.
rewrite last_rcons => e; subst w; case: leP => // lt_q; exfalso.
have pr := path_rev pq.
have e1 (V : nmodType) (f : {set G} -> V) : cycle_sum f (u :: s ++ v :: rev q) =
    (walk_sum f u (rcons s v) + walk_sum f u (rcons q v))%R.
  by rewrite cycle_sum_cat2 walk_sum_rev.
have l1 : ~~ odd_walk (u :: s ++ v :: rev q).
  apply/negP => o1; have := le_c _ _ o1; rewrite cycle_cat2 ps pr => /(_ isT).
  rewrite e1 cycle_sum_cat2 lerD2l leNgt => /negP[]; exact: lt_le_trans lt_q le_st.
have l2 : ~~ odd_walk (u :: q ++ v :: t).
  apply/negP => o2; have := le_c _ _ o2; rewrite cycle_cat2 pq pt => /(_ isT).
  by rewrite !cycle_sum_cat2 lerD2r leNgt lt_q.
move: oc l1 l2; rewrite /odd_walk e1 !cycle_sum_cat2 !oddD.
by case: (odd _); case: (odd _); case: (odd _).
Qed.

(** A lightest odd closed walk is a geodesic cycle. *)
Lemma lightest_odd_geodesic c : lightest_odd c -> geodesic_cycle ell c.
Proof.
move=> lc; have [uc oc _] := lc; split.
  rewrite -[main.seq_cycle _ _]/(ucycleb _ _ && _) /ucycleb uc.
  case: c {lc} uc oc => [|x [|y [|z c]]] //=.
  - by rewrite /odd_walk /cycle_sum big_nil.
  - by rewrite /ucycle /= sg_irrefl.
  - rewrite /odd_walk /cycle_sum /seq_cycle_edge_list /= !big_cons big_nil addr0 /=.
    by rewrite setUC oddD addbb.
move=> u v uC vC; have [<-|uv] := eqVneq u v.
  by exists [::]; split=> //; apply: shortest_walk_nil.
have [n s t _ _ e] : rot_to_arc_spec c u v by apply: rot_to_arc => //; case/andP: uc.
move: (lightest_odd_rot n lc); rewrite e => {}lc.
have eC := perm_mem (perm_seq_cycle_edge_list_rot n c).
have [le_st|/ltW le_ts] := leP (walk_sum ell u (rcons s v)) (walk_sum ell v (rcons t u)).
  exists (rcons s v); split; first exact: lighter_arc lc le_st.
  by move=> d dp; rewrite -[_ \in _]/(d \in seq_cycle_edge_list c) -eC e
    seq_cycle_edge_list_cat mem_cat dp.
exists (rcons (rev t) v); split.
  apply: shortest_walk_rev; apply: lighter_arc le_ts.
  by have := lightest_odd_rot (size (u :: s)) lc; rewrite -cat_cons rot_size_cat.
move=> d; rewrite -[_ \in _]/(d \in seq_edge_list _) -rev_cons -rev_rcons.
rewrite seq_edge_list_rev mem_rev => dt; rewrite -[_ \in _]/(d \in seq_cycle_edge_list c) -eC e.
by rewrite seq_cycle_edge_list_cat mem_cat orbC dt.
Qed.

End Lightest.
