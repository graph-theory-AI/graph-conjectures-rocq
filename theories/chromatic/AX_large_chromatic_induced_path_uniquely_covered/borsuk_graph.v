(** * A discrete Borsuk graph

    The vertices are the points of the grid [0, 2m]^(t+1), whose centre is (m, ..., m); the
    antipode of [v] is [2m - v].  Two vertices far from the centre are adjacent if one is at
    distance at most [l] from the antipode of the other (the distance of two points is the
    maximum of the distances of their coordinates).

    There is no colouring with [t] colours if [m] and [l] are large enough ([borsuk_coloring]): this
    is a discrete form of the theorem of Lyusternik and Shnirelman on the covers of the sphere,
    and it follows from Tucker's lemma.  The relation [step] satisfies the hypotheses of
    [obstruction.v] ([step_comparable], [step_stable]). *)

From GraphTheory Require Import digraph sgraph dom.
From mathcomp Require Import boot zify_ssreflect.
From GC.GraphLib Require Import tucker.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** The distance of two natural numbers. *)
Local Abbreviation dist a b := ((a - b) + (b - a)).

Lemma leqD_dist a b c : dist a c <= dist a b + dist b c.
Proof. lia. Qed.

(** Numbers at distance at most [k] are equal if they are equal modulo [k+1]. *)
Lemma eq_mod_dist a b k : a = b %[mod k.+1] -> dist a b <= k -> a = b.
Proof.
wlog le_ba : a b / b <= a => [hw eq_ab le_k|].
  by case/orP: (leq_total b a) => [/hw->|/hw->] //; rewrite addnC.
move/eqP; rewrite eqn_mod_dvd // => dvd_ab.
by have [|/dvdn_leq/(_ dvd_ab)] := posnP (a - b); lia.
Qed.

(** ** From the cube to the sphere *)

(** The point of [m - R, m + R] nearest to [a]. *)
Definition clip (m R a : nat) : nat := minn (maxn a (m - R)) (m + R).

(** The point [coord m R x] of Z^(t+1), for [x] in [0, 2m]^k and [k <= t], is at L1 distance [R]
    from the centre (m, ..., m).  Its coordinates are those of [x], as long as this is possible;
    then comes a coordinate at least [m], and the last coordinates are [m]. *)
Fixpoint coord (m R : nat) (x : seq nat) (j : nat) : nat :=
  if x is a :: x' then
    if j is j'.+1 then coord m (R - dist (clip m R a) m) x' j' else clip m R a
  else if j is 0 then m + R else m.

Section Coord.
Variable m : nat.
Implicit Types a d R : nat.

Lemma clip_le R a : R <= m -> dist (clip m R a) m <= R.
Proof. by rewrite /clip; lia. Qed.

Lemma clip_extreme R a : R <= m -> (a == 0) || (a == 2 * m) -> dist (clip m R a) m = R.
Proof. by rewrite /clip; lia. Qed.

Lemma clip_sub R a : R <= m -> a <= 2 * m -> clip m R (2 * m - a) = 2 * m - clip m R a.
Proof. by rewrite /clip; lia. Qed.

Lemma clip_close R R' a a' d :
  dist R R' <= d -> dist a a' <= d -> dist (clip m R a) (clip m R' a') <= d.
Proof. by rewrite /clip; lia. Qed.

Lemma coord0 x j : coord m 0 x j = m.
Proof.
elim: x j => [|a x IH] [|j] //=; rewrite ?addn0 ?IH //.
by rewrite /clip; lia.
Qed.

Lemma coord_le R x j : R <= m -> dist (coord m R x j) m <= R.
Proof.
elim: x R j => [|a x IH] R [|j] /= le_Rm; rewrite ?clip_le //; try lia.
apply: leq_trans (IH _ _ _) (leq_subr _ _); exact: leq_trans (leq_subr _ _) le_Rm.
Qed.

(** The images of [x, 2m], [x, 0] and [x, i]. *)

Lemma coord_top R x j : R <= m -> coord m R (rcons x (2 * m)) j = coord m R x j.
Proof.
elim: x R j => [|a x IH] R [|j] le_Rm //=.
- by rewrite /clip; lia.
- by rewrite clip_extreme ?eqxx ?orbT // subnn; case: j; rewrite ?addn0.
- by rewrite IH // (leq_trans (leq_subr _ _)).
Qed.

Lemma coord_bottom R x j : R <= m -> all (leq^~ (2 * m)) x ->
  coord m R (rcons x 0) j = 2 * m - coord m R (map (subn (2 * m)) x) j.
Proof.
elim: x R j => [|a x IH] R [|j] le_Rm /=.
- by rewrite /clip; lia.
- by rewrite clip_extreme // subnn; case: j => [|j] _; lia.
- by case/andP=> le_a _; rewrite clip_sub // subKn //; have := clip_le a le_Rm; lia.
- case/andP=> le_a le_x; rewrite IH ?(leq_trans (leq_subr _ _)) //.
  rewrite clip_sub // (_ : dist (2 * m - _) m = dist (clip m R a) m) //.
  by have := clip_le a le_Rm; lia.
Qed.

Lemma coord_extreme R x i k j :
  R <= m -> extreme (2 * m) x -> coord m R (rcons x i) j = coord m R (rcons x k) j.
Proof.
elim: x R j => [|a x IH] R [|j] le_Rm //= /orP[ext_a | ext_x].
  by rewrite clip_extreme // subnn !coord0.
by rewrite IH // (leq_trans (leq_subr _ _)).
Qed.

(** Close points of the cube have close images. *)
Lemma coord_close R R' d x x' j :
  0 < d -> dist R R' <= d -> close x x' ->
  dist (coord m R x j) (coord m R' x' j) <= d * 2 ^ size x.
Proof.
elim: x x' R R' d j => [|a x IH] [|a' x'] R R' d j //= d0 leRR'.
  by case: j => [|j] /=; lia.
case/andP=> /andP[aa' a'a] cl.
have cl_a : dist (clip m R a) (clip m R' a') <= d by rewrite clip_close //; lia.
case: j => [|j] /=; first by rewrite (leq_trans cl_a) // leq_pmulr ?expn_gt0.
rewrite expnS mulnCA mulnA; apply: IH cl; first by rewrite muln_gt0.
lia.
Qed.

(** A coordinate is far from [m]. *)
Lemma coord_far R x : exists2 j, j <= size x & R <= 2 ^ size x * dist (coord m R x j) m.
Proof.
elim: x R => [|a x IH] R /=; first by exists 0 => //; lia.
have [small|large] := leqP R (2 * dist (clip m R a) m).
  exists 0 => //=; apply: leq_trans small _.
  by rewrite leq_mul2r expnS leq_pmulr ?expn_gt0 ?orbT.
have [j lt_j le_j] := IH (R - dist (clip m R a) m); exists j.+1 => //=.
by rewrite expnS -mulnA; lia.
Qed.

End Coord.

(** ** The graph *)

Section Graph.
Variables t m l : nat.

(** Vertices at a larger distance from the centre are said to be far. *)
Definition far_dist : nat := l + 2 * l * (2 * l).+1 ^ t.+1.

Definition vertex : finType := {ffun 'I_t.+1 -> 'I_(2 * m).+1}.
Implicit Types u v w : vertex.

Definition antipode v : vertex := [ffun j => rev_ord (v j)].
Definition far v : bool := [exists j, far_dist < dist (v j) m].
Definition near d u v : bool := [forall j, dist (u j) (v j) <= d].

Lemma antipodeE v (j : 'I_t.+1) : antipode v j = 2 * m - v j :> nat.
Proof. by rewrite ffunE. Qed.

Lemma antipodeK : involutive antipode.
Proof. by move=> v; apply/ffunP => j; rewrite !ffunE rev_ordK. Qed.

Lemma far_antipode v : far (antipode v) = far v.
Proof.
by apply: eq_existsb => j; rewrite antipodeE; have := ltn_ord (v j); lia.
Qed.

Lemma near_sym d u v : near d u v = near d v u.
Proof. by apply: eq_forallb => j; rewrite addnC. Qed.

Lemma near_antipode d u v : near d (antipode u) (antipode v) = near d u v.
Proof.
apply: eq_forallb => j; rewrite !antipodeE.
by have := ltn_ord (u j); have := ltn_ord (v j); lia.
Qed.

Definition borsuk_rel : rel vertex := fun u v => [&& far u, far v & near l u (antipode v)].

Lemma borsuk_sym : symmetric borsuk_rel.
Proof.
by move=> u v; rewrite /borsuk_rel near_sym -near_antipode antipodeK andbCA.
Qed.

Lemma far_not_near v : far v -> ~~ near l v (antipode v).
Proof.
case/existsP=> j far_j; apply/negP => /forallP/(_ j); rewrite antipodeE.
by have := ltn_ord (v j); move: far_j; rewrite /far_dist; lia.
Qed.

Lemma borsuk_irrefl : irreflexive borsuk_rel.
Proof.
by move=> v; apply/negP => /and3P[far_v _]; apply/negP; exact: far_not_near.
Qed.

Definition borsuk_graph : sgraph := SGraph borsuk_sym borsuk_irrefl.

(** ** The relation *)

(** Two vertices with a common neighbour are at distance at most [2l], hence they are equal if
    their coordinates are equal modulo [2l+1].  Vertices at distance at most [2l] are directed
    according to an arbitrary order of the [(2l+1)^(t+1)] residues: the length of the directed
    paths is smaller than this number. *)
Definition residue v : {ffun 'I_t.+1 -> 'I_(2 * l).+1} := [ffun j => inord (v j %% (2 * l).+1)].
Definition rank v : nat := enum_rank (residue v).
Definition step u v : bool := near (2 * l) u v && (rank u < rank v).

Lemma rank_lt v : rank v < (2 * l).+1 ^ t.+1.
Proof. by apply: leq_trans (ltn_ord _) _; rewrite card_ffun !card_ord. Qed.

Lemma connect_near u v (j : 'I_t.+1) :
  connect step u v -> dist (u j) (v j) + 2 * l * rank u <= 2 * l * rank v.
Proof.
case/connectP=> p + ->; elim: p u => [|w p IH] u /=; first by lia.
case/andP=> /andP[/forallP/(_ j) near_uw lt_uw] /IH.
apply: leq_trans; apply: leq_trans (leq_add (leqD_dist _ (w j) _) (leqnn _)) _.
rewrite addnAC [leqRHS]addnC leq_add2r.
by apply: leq_trans (leq_mul (leqnn (2 * l)) lt_uw); rewrite mulnS leq_add2r.
Qed.

(** The vertices reachable from [v] are near [v]: no two of them are almost antipodal. *)
Lemma step_stable v : @stable borsuk_graph [set w | connect step v w].
Proof.
apply/stableP => u w; rewrite !inE => cu cw; apply/negP => /and3P[/existsP[j far_j] _].
move/forallP/(_ j); rewrite antipodeE => near_uw.
have := connect_near j cu; have := connect_near j cw.
have := leq_mul (leqnn (2 * l)) (ltnW (rank_lt u)).
have := leq_mul (leqnn (2 * l)) (ltnW (rank_lt w)).
by move: far_j near_uw; rewrite /far_dist; lia.
Qed.

Lemma step_comparable (u v w : borsuk_graph) :
  u -- v -> v -- w -> connect step u w || connect step w u.
Proof.
rewrite [v -- w]sgP => /and3P[_ _ near_u] /and3P[_ _ near_w].
have near_uw : near (2 * l) u w.
  by apply/forallP => j; move/forallP/(_ j): near_u; move/forallP/(_ j): near_w; lia.
have [lt_uw | lt_wu | eq_uw] := ltngtP (rank u) (rank w).
- by rewrite connect1 // /step near_uw.
- by rewrite orbC connect1 // /step near_sym near_uw.
- suff -> : u = w by rewrite connect0.
  have /ffunP eq_res := enum_rank_inj (val_inj eq_uw).
  apply/ffunP => j; apply/val_inj/(@eq_mod_dist _ _ (2 * l)); last exact: (forallP near_uw).
  by have /(congr1 val) := eq_res j; rewrite !ffunE /= !inordK ?ltn_pmod.
Qed.

(** ** The chromatic number *)

Hypothesis l_large : 2 ^ t <= l.
Hypothesis m_large : 2 ^ t * far_dist < m.

(** The vertex given by a point of the cube [0, 2m]^k. *)
Definition vertex_of (x : seq nat) : vertex := [ffun j : 'I_t.+1 => inord (coord m m x j)].

Lemma vertex_ofE x j : vertex_of x j = coord m m x j :> nat.
Proof. by rewrite ffunE inordK //; have := coord_le x j (leqnn m); lia. Qed.

Lemma vertex_of_far x : size x <= t -> far (vertex_of x).
Proof.
move=> le_xt; have [j le_j le_m] := coord_far m m x.
apply/existsP; exists (inord j); rewrite vertex_ofE inordK ?ltnS ?(leq_trans le_j) //.
rewrite ltnNge; apply/negP => le_far; have := leq_trans m_large le_m.
by rewrite ltnNge leq_mul ?leq_pexp2l.
Qed.

(** The colours of a colouring give labels: if [pos v], then the label of [v] is the colour of [v]
    and its antipode has the complementary label. *)
Lemma borsuk_coloring (col : borsuk_graph -> 'I_t) :
  ~ forall u v : borsuk_graph, u -- v -> col u != col v.
Proof.
move=> colP.
pose pos v := enum_rank v < enum_rank (antipode v).
pose lab x :=
  let v := vertex_of x in
  if pos v then (col v : nat, true) else (col (antipode v) : nat, false).
have pt_le k x : k <= t -> point (2 * m) k x -> size x <= t by move=> le_k /andP[/eqP->].
have pos_antipode v : far v -> pos (antipode v) = ~~ pos v.
  move=> far_v; rewrite /pos antipodeK -leqNgt [RHS]leq_eqVlt.
  case: eqP => // eq_rank; have eq_v := enum_rank_inj (ord_inj eq_rank).
  have := far_not_near far_v; rewrite eq_v => /negP[].
  by apply/forallP => j; rewrite subnn.
have lab_eq x y : (forall j, coord m m x j = coord m m y j) -> lab x = lab y.
  move=> eq_c; suff eq_xy : vertex_of x = vertex_of y by rewrite /lab eq_xy.
  by apply/ffunP => j; rewrite !ffunE eq_c.
apply: (@tucker (2 * m) t lab).
- by move=> k x _ _; rewrite /lab; case: ifP => _; exact: ltn_ord.
- by move=> k x _ _; apply: lab_eq => j; rewrite coord_top.
- move=> k x lt_k pt_x; have /andP[_ le_x] := pt_x; set x' := map _ x.
  have eq_v : vertex_of (rcons x 0) = antipode (vertex_of x').
    by apply/ffunP => j; apply: val_inj; rewrite /= antipodeE !vertex_ofE coord_bottom.
  have far_v : far (vertex_of x').
    by apply: vertex_of_far; rewrite size_map (pt_le _ _ (ltnW lt_k) pt_x).
  by rewrite /lab /= eq_v antipodeK pos_antipode //; case: (pos _).
- by move=> x i j ext_x; apply: lab_eq => c; apply: coord_extreme.
move=> k x y le_k /(pt_le _ _ le_k) le_x /(pt_le _ _ le_k) le_y cl_xy.
have near_xy : near l (vertex_of x) (vertex_of y).
  apply/forallP => j; rewrite !vertex_ofE; apply: leq_trans l_large.
  apply: (@leq_trans (1 * 2 ^ size x)); last by rewrite mul1n leq_pexp2l.
  by apply: coord_close; rewrite // subnn.
have edge u v : far u -> far v -> near l u v -> col u != col (antipode v).
  move=> far_u far_v near_uv; apply: colP.
  by rewrite /edge_rel /= /borsuk_rel far_u far_antipode far_v antipodeK.
have far_x := vertex_of_far le_x; have far_y := vertex_of_far le_y.
rewrite /lab /opposite; case: ifP => _; case: ifP => _ //= [] /val_inj eq_col.
  by have := edge _ _ far_x far_y near_xy; rewrite eq_col eqxx.
by rewrite near_sym in near_xy; have := edge _ _ far_y far_x near_xy; rewrite eq_col eqxx.
Qed.

End Graph.
