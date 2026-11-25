(** * A Tucker lemma on a grid

    A label is a pair of an index [a : nat] and a sign; two labels are complementary if they have
    the same index and opposite signs.  The points are the sequences of [k] numbers in [0, M], and
    the vertices of a simplex are points whose coordinates pairwise differ by at most one.
    Lemma [tucker]: let the points with [k <= t] coordinates be labelled with indices smaller
    than [t], such that, for [x] a point with less than [t] coordinates,
    - [x, M] has the label of [x], and [x, 0] has the complement of the label of [M - x];
    - the label of [x, i] does not depend on [i] when a coordinate of [x] is 0 or [M].
    Then two points of a simplex have complementary labels.

    The proof is the combinatorial proof by Ky Fan of Tucker's lemma, with chains modulo 2.  A
    cochain is a boolean function on sequences of points.  The cube [0, M]^k.+1 is triangulated by
    prisms over the simplices of [0, M]^k, and [grid k c] is the sum of the cochain [c] over the
    simplices of this triangulation.  If there are no complementary labels, then, for all [k <= t],
    there is an odd number of simplices whose [k.+1] labels have alternating signs when sorted by
    their indices; this is absurd for [k = t]. *)

From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Coboundary and prisms *)

Lemma perm_rem (A : eqType) (x : A) (s s' : seq A) : perm_eq s s' -> perm_eq (rem x s) (rem x s').
Proof. by move=> /permP eq_s; apply/allP => y _ /=; rewrite !count_mem_rem eq_s. Qed.

(** The sum of [c] over the faces of [s]. *)
Fixpoint cobd (A : eqType) (c : seq A -> bool) (s : seq A) : bool :=
  if s is x :: s' then c s' (+) cobd (c \o cons x) s' else false.

Section Cochains.
Variables A B : eqType.

(** The sum of [c] over the simplices [f x_0, ..., f x_i, g x_i, ..., g x_k], where
    s = [x_0, ..., x_k]. *)
Fixpoint prism (f g : A -> B) (c : seq B -> bool) (s : seq A) : bool :=
  if s is x :: s' then c (f x :: g x :: map g s') (+) prism f g (c \o cons (f x)) s' else false.

Lemma eq_cobd (c c' : seq A -> bool) (s : seq A) :
  (forall u, {subset u <= s} -> c u = c' u) -> cobd c s = cobd c' s.
Proof.
elim: s c c' => //= x s IH c c' eq_c; congr (_ (+) _).
  by apply: eq_c => y ys; rewrite inE ys orbT.
apply: IH => u us; apply: eq_c => y; rewrite !inE => /orP[->//|/us->]; exact: orbT.
Qed.

Lemma cobd0 (s : seq A) : cobd xpred0 s = false.
Proof. by elim: s. Qed.

Lemma cobdD (c c' : seq A -> bool) (s : seq A) :
  cobd (fun u => c u (+) c' u) s = cobd c s (+) cobd c' s.
Proof. by elim: s c c' => //= x s IH c c'; rewrite IH addbACA. Qed.

Lemma cobd_map (f : A -> B) (c : seq B -> bool) (s : seq A) :
  cobd c (map f s) = cobd (c \o map f) s.
Proof. by elim: s c => //= x s IH c; rewrite IH. Qed.

(** The coboundary of a symmetric cochain is symmetric. *)
Lemma perm_cobd (c : seq A -> bool) (s s' : seq A) :
  (forall u u', perm_eq u u' -> c u = c u') -> perm_eq s s' -> cobd c s = cobd c s'.
Proof.
move=> symc; suff cobdE u : cobd c u = \big[addb/false]_(x <- u) c (rem x u).
  move=> eq_s; rewrite !cobdE (perm_big _ eq_s) /=; apply: eq_big_seq => x _.
  exact/symc/perm_rem.
elim: u c symc => [|x u IH] c symc; first by rewrite big_nil.
rewrite big_cons /= eqxx IH => [v v' eq_v|]; first by apply: symc; rewrite perm_cons.
congr addb; apply: eq_big_seq => y yu; apply: symc; case: eqP => [->|_] //.
by rewrite perm_sym perm_to_rem.
Qed.

Variables f g : A -> B.

(** The simplices of the prism have one vertex more, of the form [f x] or [g x]. *)
Lemma eq_prism (c c' : seq B -> bool) (s : seq A) :
  (forall u, size u = (size s).+1 ->
     (forall y, y \in u -> exists2 x, x \in s & y = f x \/ y = g x) -> c u = c' u) ->
  prism f g c s = prism f g c' s.
Proof.
elim: s c c' => //= x s IH c c' eq_c; congr (_ (+) _).
  apply: eq_c => [|y]; first by rewrite /= size_map.
  rewrite !inE => /or3P[/eqP->|/eqP->|/mapP[z zs ->]].
  - by exists x; [rewrite mem_head | left].
  - by exists x; [rewrite mem_head | right].
  - by exists z; [rewrite inE zs orbT | right].
apply: IH => u sz_u vu; apply: eq_c => [|y]; first by rewrite /= sz_u.
rewrite inE => /orP[/eqP->|/vu[z zs eq_y]]; first by exists x; [rewrite mem_head | left].
by exists z => //; rewrite inE zs orbT.
Qed.

Lemma prism0 (s : seq A) : prism f g xpred0 s = false.
Proof. by elim: s. Qed.

Lemma prismD (c c' : seq B -> bool) (s : seq A) :
  prism f g (fun u => c u (+) c' u) s = prism f g c s (+) prism f g c' s.
Proof. by elim: s c c' => //= x s IH c c'; rewrite IH addbACA. Qed.

Lemma prism_degenerate (c : seq B -> bool) (s : seq A) :
  (forall x u v, x \in s -> c (u ++ f x :: g x :: v) = false) -> prism f g c s = false.
Proof.
elim: s c => //= x s IH c c0; rewrite (c0 x [::]) ?mem_head //.
by apply: IH => y u v ys; apply: (c0 y (f x :: u)); rewrite inE ys orbT.
Qed.

(** The boundary of a prism. *)
Lemma prism_cobd (c : seq B -> bool) (s : seq A) :
  prism f g (cobd c) s =
  c (map f s) (+) c (map g s) (+) cobd (prism f g c) s.
Proof.
elim: s c => [|x s IH] c /=; first by rewrite addbb.
rewrite (@eq_prism _ (fun u => c u (+) cobd (c \o cons (f x)) u)) // prismD IH /=.
rewrite [cobd (_ \o _) s]
  (@eq_cobd _ (fun u => c (f x :: g x :: map g u) (+) prism f g (c \o cons (f x)) u)) //.
rewrite cobdD cobd_map /=.
rewrite -[cobd ((c \o _) \o _ \o _) s]/(cobd (fun u => c (f x :: g x :: map g u)) s).
set a := c (g x :: _); set b := c (f x :: map g s); set e := cobd _ s; set h := prism f g c s.
set i := c _; set j := cobd _ s.
by case: a b e h i j => [] [] [] [] [] [].
Qed.

Lemma prism_rcons (c : seq B -> bool) (s : seq A) (x : A) :
  prism f g c (rcons s x) =
  prism f g (fun u => c (rcons u (g x))) s (+) c (rcons (rcons (map f s) (f x)) (g x)).
Proof.
elim: s c => [|y s IH] c /=; first by rewrite addbF.
by rewrite IH /= map_rcons addbA.
Qed.

End Cochains.

Lemma prism_rev (A B : eqType) (f g : A -> B) (c : seq B -> bool) (s : seq A) :
  prism f g (c \o rev) s = prism g f c (rev s).
Proof.
elim: s c => //= x s IH c; rewrite (rev_cons x) prism_rcons addbC; congr (_ (+) _).
  by rewrite -IH; apply: eq_prism => u _ _ /=; rewrite rev_cons.
by rewrite !rev_cons map_rev.
Qed.

Lemma prism_map (A A' B B' : eqType) (h : A -> A') (h' : B -> B') (f g : A -> B) (f' g' : A' -> B')
    (c : seq B' -> bool) (s : seq A) :
  h' \o f =1 f' \o h -> h' \o g =1 g' \o h ->
  prism f g (c \o map h') s = prism f' g' c (map h s).
Proof.
move=> eq_f eq_g; elim: s c => //= x s IH c; have /= eq_fx := eq_f x.
by rewrite -IH -eq_fx -map_comp (eq_map eq_g) map_comp -[g' (h x)]eq_g.
Qed.

(** ** Alternating sequences of labels *)

Definition opposite (a : nat * bool) : nat * bool := (a.1, ~~ a.2).

(** The indices in [l] are smaller than [j] and distinct and, by decreasing index, the signs
    alternate, beginning with [s]. *)
Fixpoint alternating (j : nat) (s : bool) (l : seq (nat * bool)) : bool :=
  if j is j'.+1 then
    if (j', s) \in l then alternating j' (~~ s) (rem (j', s) l) else alternating j' s l
  else nilp l.

Lemma perm_alternating j s l l' : perm_eq l l' -> alternating j s l = alternating j s l'.
Proof.
elim: j s l l' => [|j IH] s l l' eq_l /=; first by rewrite /nilp (perm_size eq_l).
by rewrite (perm_mem eq_l) (IH _ _ _ eq_l) (IH (~~ s) _ _ (perm_rem _ eq_l)).
Qed.

Lemma alternating_lt j s l a : alternating j s l -> a \in l -> a.1 < j.
Proof.
elim: j s l => [|j IH] s l /=; first by rewrite /nilp size_eq0 => /eqP->.
case: ifP => [js alt_l | _ alt_l al]; last exact/ltnW/(IH _ _ alt_l al).
rewrite (perm_mem (perm_to_rem js)) inE => /orP[/eqP->//|al].
exact/ltnW/(IH _ _ alt_l al).
Qed.

Lemma alternating_size j s l : alternating j s l -> size l <= j.
Proof.
elim: j s l => [|j IH] s l /=; first by rewrite /nilp => /eqP->.
case: ifP => [js /IH | _ /IH /leqW//].
by rewrite -ltnS size_rem // prednK // -has_predT; apply/hasP; exists (j, s).
Qed.

Lemma alternating_uniq j s l : alternating j s l -> uniq l.
Proof.
elim: j s l => [|j IH] s l /=; first by rewrite /nilp size_eq0 => /eqP->.
case: ifP => [js alt_l | _]; last exact: IH.
rewrite (perm_uniq (perm_to_rem js)) /= (IH _ _ alt_l) andbT.
by apply/negP => /(alternating_lt alt_l); rewrite ltnn.
Qed.

Lemma alternating_opposite j s l : alternating j s (map opposite l) = alternating j (~~ s) l.
Proof.
have opK : involutive opposite by case=> a b; rewrite /opposite negbK.
elim: j s l => [|j IH] s l /=; first by rewrite /nilp size_map.
have -> : (j, s) = opposite (j, ~~ s) by rewrite /opposite negbK.
rewrite (mem_map (can_inj opK)) IH; case: ifP => // jl.
rewrite -[RHS]IH; apply: perm_alternating; rewrite -(perm_cons (opposite (j, ~~ s))).
rewrite -(permPl (perm_to_rem _)); first by rewrite map_f.
exact: (perm_map opposite (perm_to_rem jl)).
Qed.

Lemma alternating1 j s a : alternating j s [:: a] = (a.1 < j) && (a.2 == s).
Proof.
elim: j s => [|j IH] s //=; rewrite inE IH ltnS eq_sym [a.1 <= j]leq_eqVlt.
rewrite -pair_eqE /pair_eq /=; case: eqP => //= _; case: eqP => [_ | _]; last by rewrite andbF.
by elim: j (~~ s) {IH} => //=.
Qed.

(** Among the faces of [l], there is an odd number of alternating sequences beginning with [s]
    if and only if [l] is alternating. *)
Lemma cobd_alternating j s l :
  {in l, forall a, a.1 < j} -> {in l, forall a, opposite a \notin l} ->
  cobd (alternating j s) l = alternating j true l (+) alternating j false l.
Proof.
elim: j s l => [|j IH] s l lt_l nopp.
  by case: l lt_l {nopp} => // a l /(_ a (mem_head _ _)).
have altS r u : (j, r) \notin u -> alternating j.+1 r u = alternating j r u.
  by move=> /= /negbTE->.
have [[r jl] | nojl] : (exists r, (j, r) \in l) \/ forall r, (j, r) \notin l.
- have [jt | nt] := boolP ((j, true) \in l); first by left; exists true.
  have [jf | nf] := boolP ((j, false) \in l); first by left; exists false.
  by right; case.
- have nrl : (j, ~~ r) \notin l by exact: (nopp _ jl).
  move: (perm_to_rem jl); set l' := rem _ l => eq_l.
  have sub_l : {subset l' <= l} by move=> a al'; rewrite (perm_mem eq_l) inE al' orbT.
  have not_alt i b u : (i, b) \in u -> alternating i (~~ r) u = false.
    by move=> iu; apply/negP => /alternating_lt/(_ iu); rewrite ltnn.
  have -> : alternating j.+1 true l (+) alternating j.+1 false l = alternating j (~~ r) l'.
    transitivity (alternating j.+1 r l (+) alternating j.+1 (~~ r) l).
      by case: (r) => //; rewrite addbC.
    by rewrite [alternating _ (~~ r) _]altS // (not_alt _ _ _ jl) addbF /= jl.
  rewrite (perm_cobd (@perm_alternating _ _) eq_l).
  have [jl' | njl'] := boolP ((j, r) \in l').
    rewrite (not_alt _ _ _ jl').
    have /(perm_cobd (@perm_alternating j.+1 s))-> :
        perm_eq ((j, r) :: l') [:: (j, r), (j, r) & rem (j, r) l'].
      by rewrite perm_cons perm_to_rem.
    rewrite /= addbA addbb -[RHS](cobd0 (rem (j, r) l')); apply: eq_cobd => u _.
    by apply/negP => /(@alternating_uniq j.+1) /=; rewrite mem_head.
  have nrl' : (j, ~~ r) \notin l' by apply: contra nrl; exact: sub_l.
  have lt_l' : {in l', forall a, a.1 < j}.
    move=> a al'; have := lt_l _ (sub_l _ al'); rewrite ltnS leq_eqVlt => /orP[/eqP eq_a|//].
    by case: a eq_a al' => a [] /= ->; case: (r) njl' nrl' => /negPf n1 /negPf n2; rewrite ?n1 ?n2.
  have nopp' : {in l', forall a, opposite a \notin l'}.
    by move=> a /sub_l/nopp; apply: contra; exact: sub_l.
  have [-> | ->] : s = r \/ s = ~~ r by case: (s) (r) => [] []; [left|right|right|left].
    rewrite [LHS]/= -/(alternating j.+1 r l') altS //.
    rewrite [cobd _ _](@eq_cobd _ _ (alternating j (~~ r))) => [u _|].
      by rewrite /= mem_head eqxx.
    by rewrite IH //; case: (r); [rewrite addKb | rewrite addbC addbK].
  rewrite [LHS]/= -/(alternating j.+1 (~~ r) l') altS //.
  rewrite [cobd _ _](@eq_cobd _ _ xpred0) => [u ul'|]; last by rewrite cobd0 addbF.
  rewrite -[LHS]/(alternating j.+1 (~~ r) ((j, r) :: u)) altS ?(not_alt _ _ _ (mem_head _ _)) //.
  rewrite inE xpair_eqE eqxx andTb orbC; case: eqP => [|_]; first by case: (r).
  by rewrite orbF; apply: contra nrl'; exact: ul'.
- have lt_l' : {in l, forall a, a.1 < j}.
    move=> [a b] al; have := lt_l _ al; rewrite ltnS leq_eqVlt => /orP[/eqP /= eq_a|//].
    by have := nojl b; rewrite -eq_a al.
  rewrite !altS // -(IH s) //.
  by apply: eq_cobd => u ul; rewrite altS //; apply: contra (nojl s); exact: ul.
Qed.

(** ** The triangulated grid *)

(** The points [x] and [y] have coordinates that pairwise differ by at most one. *)
Definition close (x y : seq nat) : bool := all2 (fun a b => (a <= b.+1) && (b <= a.+1)) x y.

Lemma close_rcons x y a b :
  close x y -> a <= b.+1 -> b <= a.+1 -> close (rcons x a) (rcons y b).
Proof.
elim: x y => [|c x IH] [|d y] //=; first by move=> _ -> ->.
by case/andP=> -> cl ab ba; exact: IH.
Qed.

Section Grid.
Variable M : nat.

(** [x] is a point of [0, M]^k. *)
Definition point (k : nat) (x : seq nat) : bool := (size x == k) && all (leq^~ M) x.

(** The sum of [c] over the simplices of [0, M]^k. *)
Fixpoint grid (k : nat) (c : seq (seq nat) -> bool) : bool :=
  if k is k'.+1 then
    \big[addb/false]_(i < M) grid k' (prism (rcons^~ (i : nat)) (rcons^~ i.+1) c)
  else c [:: [::]].

(** The simplices of [0, M]^k satisfy this property. *)
Definition simplex (k : nat) (s : seq (seq nat)) : Prop :=
  [/\ size s = k.+1, {in s, forall x, point k x} & {in s &, forall x y, close x y}].

Lemma eq_grid k c c' : (forall s, simplex k s -> c s = c' s) -> grid k c = grid k c'.
Proof.
elim: k c c' => [|k IH] c c' eq_c /=.
  by apply: eq_c; split=> // x; [|move=> y]; rewrite !inE => /eqP-> // /eqP->.
apply: eq_bigr => i _; apply: IH => s [sz_s pt_s cl_s]; apply: eq_prism => u sz_u vu.
apply: eq_c; split=> [|x /vu[z zs eq_x] | x y /vu[z zs eq_x] /vu[w ws eq_y]].
- by rewrite sz_u sz_s.
- case/andP: (pt_s _ zs) => /eqP sz_z le_z; case: eq_x => ->.
  + by rewrite /point size_rcons sz_z eqxx all_rcons le_z ltnW.
  + by rewrite /point size_rcons sz_z eqxx all_rcons le_z ltn_ord.
- have cl := cl_s _ _ zs ws.
  by case: eq_x => ->; case: eq_y => ->; apply: close_rcons => //; exact/leqW/leqnSn.
Qed.

Lemma gridD k c c' : grid k (fun s => c s (+) c' s) = grid k c (+) grid k c'.
Proof.
elim: k c c' => [|k IH] c c' //=; rewrite -big_split /=; apply: eq_bigr => i _.
by rewrite -IH; apply: eq_grid => s _; exact: prismD.
Qed.

Lemma grid0 k : grid k xpred0 = false.
Proof.
elim: k => //= k IH; rewrite big1 // => i _; rewrite -[RHS]IH.
by apply: eq_grid => s _; exact: prism0.
Qed.

(** The grid is symmetric: the symmetry reverses the order of the vertices. *)
Lemma grid_rev k c : grid k (c \o rev \o map (map (subn M))) = grid k c.
Proof.
elim: k c => [|k IH] c //=; rewrite (reindex_inj rev_ord_inj) /=; apply: eq_bigr => i _.
rewrite -[RHS]IH; apply: eq_grid => s _ /=; rewrite -[RHS]prism_rev.
apply: prism_map => x /=.
  by rewrite map_rcons subKn.
by rewrite map_rcons -subSn // subKn // ltnW.
Qed.

(** The boundary of the grid: the other facets of the cube, where a coordinate before the last one
    is 0 or [M], are those of the prisms over the boundary of [0, M]^k. *)
Lemma grid_cobd k c :
  grid k.+1 (cobd c) =
  grid k (c \o map (rcons^~ 0)) (+) grid k (c \o map (rcons^~ M)) (+)
  \big[addb/false]_(i < M) grid k (cobd (prism (rcons^~ (i : nat)) (rcons^~ i.+1) c)).
Proof.
rewrite /=; transitivity (\big[addb/false]_(i < M)
    (grid k (c \o map (rcons^~ (i : nat))) (+) grid k (c \o map (rcons^~ i.+1)) (+)
     grid k (cobd (prism (rcons^~ (i : nat)) (rcons^~ i.+1) c)))).
  apply: eq_bigr => i _; rewrite -!gridD; apply: eq_grid => s _; exact: prism_cobd.
rewrite big_split /=; congr (_ (+) _).
elim: M => [|n IH]; first by rewrite big_ord0 addbb.
by rewrite big_ord_recr /= IH addbA -(addbA (grid k _)) addbb addbF.
Qed.

(** A coordinate of [x] is 0 or [M]. *)
Definition extreme (x : seq nat) : bool := has (fun a => (a == 0) || (a == M)) x.

Lemma extreme_rcons x a : extreme x -> extreme (rcons x a).
Proof. by move=> ext; rewrite /extreme has_rcons; apply/orP; right. Qed.

Lemma grid_cobd0 k c : (forall s, all extreme s -> c s = false) -> grid k (cobd c) = false.
Proof.
elim: k c => [|k IH] c c0; first by rewrite /= c0.
rewrite grid_cobd big1 => [i _|].
  apply: IH => s ext_s; rewrite -[RHS](prism0 (rcons^~ (i : nat)) (rcons^~ i.+1) s).
  apply: eq_prism => u _ vu; apply: c0; apply/allP => y /vu[x xs eq_y].
  by case: eq_y => ->; apply/extreme_rcons/(allP ext_s).
have ext0 a : (a == 0) || (a == M) -> grid k (c \o map (rcons^~ a)) = false.
  move=> ext_a; rewrite -[RHS](grid0 k); apply: eq_grid => s _; apply: c0.
  by apply/allP => y /mapP[x _ ->]; rewrite /extreme has_rcons ext_a.
by rewrite !ext0 ?eqxx ?orbT.
Qed.

(** ** Tucker's lemma *)

Variables (t : nat) (lab : seq nat -> nat * bool).
Hypothesis lab_lt : forall k x, k <= t -> point k x -> (lab x).1 < t.
Hypothesis lab_top : forall k x, k < t -> point k x -> lab (rcons x M) = lab x.
Hypothesis lab_bottom :
  forall k x, k < t -> point k x -> lab (rcons x 0) = opposite (lab (map (subn M) x)).
Hypothesis lab_extreme : forall x i j, extreme x -> lab (rcons x i) = lab (rcons x j).

Lemma tucker :
  ~ (forall k x y, k <= t -> point k x -> point k y -> close x y -> lab x <> opposite (lab y)).
Proof.
move=> nopp; pose alt s := alternating t s \o map lab.
suff odd_alt k : k <= t -> grid k (fun s => alt true s (+) alt false s).
  have := odd_alt t (leqnn t); rewrite (@eq_grid _ _ xpred0) ?grid0 // => s [sz_s _ _].
  have small b : alt b s = false.
    by apply/negP => /alternating_size; rewrite size_map sz_s ltnn.
  by rewrite !small.
elim: k => [|k IH] lt_kt.
  by rewrite /= /alt /= !alternating1 (lab_lt (k := 0)) //=; case: (lab _).2.
rewrite (@eq_grid _ _ (cobd (alt true))) => [s [_ pt_s cl_s]|].
  rewrite -cobd_map cobd_alternating // => a /mapP[x xs ->]; first exact: lab_lt (pt_s _ xs).
  apply/mapP => -[y ys opp].
  apply: (nopp _ y x lt_kt (pt_s _ ys) (pt_s _ xs) (cl_s _ _ ys xs)).
  by rewrite opp.
rewrite grid_cobd big1 ?addbF => [i _|].
  apply: grid_cobd0 => s ext_s; apply: prism_degenerate => x u v xs.
  apply/negP => /alternating_uniq; rewrite map_cat cat_uniq /= (lab_extreme i i.+1) ?mem_head //.
    exact: (allP ext_s).
  by rewrite !andbF.
have -> : grid k (alt true \o map (rcons^~ 0)) = grid k (alt false).
  rewrite -[RHS]grid_rev; apply: eq_grid => s [_ pt_s _] /=.
  rewrite /alt /= map_rev (perm_alternating _ _ (permEl (perm_rev _))).
  rewrite -(alternating_opposite t true) -!map_comp; congr (alternating _ _ _).
  by apply/eq_in_map => x xs /=; apply: lab_bottom (pt_s _ xs).
have -> : grid k (alt true \o map (rcons^~ M)) = grid k (alt true).
  apply: eq_grid => s [_ pt_s _]; rewrite /alt /= -map_comp; congr (alternating _ _ _).
  by apply/eq_in_map => x xs /=; apply: lab_top (pt_s _ xs).
by rewrite addbC -gridD IH // ltnW.
Qed.

End Grid.
