(** * A graph without short heavy path

Main file of the disproof, which comes from Graph-Theory-LLM-Proofs (attacks/1904.12273__01).

For an odd q >= 5 and n = 3q, the graph G consists of
- a cycle C of length n, on the positions 0, ..., n - 1;
- for k = 0, 1, 2, a vertex y_k adjacent to the q + 1 positions of the arc A_k of C, which goes
  from kq to (k + 1)q (modulo n); the y_k form a triangle;
- a vertex x adjacent to all the vertices of C, and to no y_k.

Then C is a shortest odd hole of length at least 7 of G [shortest_C].  Indeed, let d be a hole of
length at least 6.  Two vertices of d that are not consecutive are not adjacent, so d does not
contain x: otherwise the second and fourth vertices of d after x would be distinct y_k, which are
adjacent.  If d contains no y_k, then d is C.  Otherwise d contains one y_k, or two which are
consecutive, and the rest of d is a path of C that leaves the arc of a y_k at its first step and
enters the arc of a y_k' at its last step.  Such a path has 2q edges if k = k', and q edges
otherwise, so that d has the even length 2q + 2 or q + 3.

The vertices of M = {x, y_0, y_1, y_2} are C-major as they have four neighbours on C, and x is
adjacent to no y_k.  But a path of C with less than q edges misses some arc A_k, hence contains
no neighbour of y_k [path_misses_arc].  As q is arbitrarily large, no constant suits ell = 7. *)

From GraphTheory Require Import digraph sgraph.
From GC.GraphLib Require Import misc.
From GC.misc.AX_long_odd_hole_heavy_path_lemma Require Import arcs.
From GC.misc.AX_long_odd_hole_heavy_path_lemma Require main.
From mathcomp Require Import boot zify.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Abbreviation long_odd_hole := main.long_odd_hole.
Abbreviation shortest_long_odd_hole := main.shortest_long_odd_hole.
Abbreviation cycle_path := main.cycle_path.
Abbreviation major := main.major.

Section Counterexample.
Variable q : nat.
Abbreviation n := (3 * q).

(** The vertices of G: the positions on C, the [y_k] ([Some k]) and [x] ([None]). *)
Definition rel_G (u v : 'I_n + option 'I_3) : bool :=
  match u, v with
  | inl i, inl j => succ_pos n i j || succ_pos n j i
  | inl i, inr (Some k) | inr (Some k), inl i => inarc q k i
  | inl _, inr None | inr None, inl _ => true
  | inr (Some k), inr (Some k') => k != k'
  | inr _, inr _ => false
  end.

Lemma rel_G_sym : symmetric rel_G.
Proof. by move=> [i|[k|]] [j|[k'|]] //=; [apply: orbC|rewrite eq_sym]. Qed.

Lemma rel_G_irrefl : irreflexive rel_G.
Proof.
move=> [i|[k|]] //=; last by rewrite eqxx.
by rewrite /succ_pos orbb; apply/negbTE; lia.
Qed.

Definition G : sgraph := SGraph rel_G_sym rel_G_irrefl.

Definition cv (i : 'I_n) : G := inl i.
Definition yv (k : 'I_3) : G := inr (Some k).
Definition xv : G := inr None.

(** The kind and the position of a vertex. *)
Definition isC (u : G) : bool := if u is inl _ then true else false.
Definition isY (u : G) : bool := if u is inr (Some _) then true else false.
Definition pos (u : G) : nat := if u is inl i then val i else 0.

Hypotheses (q_gt4 : 4 < q) (odd_q : odd q).

Lemma pos_lt u : pos u < n.
Proof. by case: u => [i|k] /=; [exact: ltn_ord|lia]. Qed.

Lemma pos_inj u v : isC u -> isC v -> pos u = pos v -> u = v.
Proof. by move: u v => [i|//] [j|//] _ _ /val_inj ->. Qed.

Lemma adj_CC u v : isC u -> isC v ->
  (u -- v) = succ_pos n (pos u) (pos v) || succ_pos n (pos v) (pos u).
Proof. by move: u v => [i|//] [j|//]. Qed.

Lemma adj_YC k u : isC u -> (yv k -- u) = inarc q k (pos u).
Proof. by case: u. Qed.

Lemma adj_YY u v : isY u -> isY v -> u != v -> u -- v.
Proof. by move: u v => [//|[k|//]] [//|[k'|//]]. Qed.

Lemma isY_yv u : isY u -> exists k, u = yv k.
Proof. by case: u => [//|[k|//]]; exists k. Qed.

(** ** The hole C *)

Definition C : seq G := map cv (enum 'I_n).

Lemma size_C : size C = n.
Proof. by rewrite size_map size_enum_ord. Qed.

Lemma mem_C u : (u \in C) = isC u.
Proof.
case: u => [i|k]; first by rewrite (mem_map (@inl_inj _ _)) mem_enum.
by apply/negbTE/mapP => -[].
Qed.

Lemma hole_C : hole C.
Proof.
apply/(hole_nthP xv); split; rewrite ?size_C.
- by rewrite (map_inj_uniq (@inl_inj _ _)) enum_uniq.
- lia.
have nth_C (i : 'I_n) : nth xv C i = cv i.
  by rewrite (nth_map i) ?size_enum_ord // nth_ord_enum.
move=> i j lt_i lt_j; have /= -> := nth_C (Ordinal lt_i); have /= -> := nth_C (Ordinal lt_j).
by rewrite adj_CC // ![_ %% _ == _]succ_posE.
Qed.

(** ** The other long odd holes are not shorter *)

(** Vertices at distance at least 2 on a hole are not adjacent. *)
Lemma adj_consecutive d i j : hole d -> i < j < size d ->
  (nth xv d i -- nth xv d j) = (j == i.+1) || ((i == 0) && (j == (size d).-1)).
Proof.
move=> /(hole_nthP xv) [_ _ adj] /andP [ij lt_j]; have lt_i := ltn_trans ij lt_j.
rewrite adj // !succ_posE // /succ_pos; lia.
Qed.

Lemma nth_neq d i j : hole d -> i < j < size d -> nth xv d i != nth xv d j.
Proof.
move=> /(hole_nthP xv) [ud _ _] /andP [ij lt_j].
by rewrite nth_uniq ?(ltn_trans ij) // ltn_eqF.
Qed.

(** Two vertices [y_k] on a hole are consecutive, since they are adjacent. *)
Lemma not_YY d i j : hole d -> i.+1 < j < size d -> ~~ ((i == 0) && (j == (size d).-1)) ->
  isY (nth xv d i) -> ~~ isY (nth xv d j).
Proof.
move=> hd /andP [ij lt_j] /negbTE ne yi; apply/negP => yj.
have ij' : i < j < size d by rewrite (ltnW ij).
by have := adj_YY yi yj (nth_neq hd ij'); rewrite adj_consecutive // ne gtn_eqF.
Qed.

(** A hole through [x] has at most 5 vertices. *)
Lemma x_notin d : hole d -> 5 < size d -> xv \notin d.
Proof.
move=> hd d6; apply/negP => /(hole_mem_rot hd) [p hp sp].
have Y j : 1 < j < 5 -> isY (nth xv (xv :: p) j).
  move=> /andP [j1 j5].
  have j0 : 0 < j < size (xv :: p) by rewrite (ltnW j1) sp (ltn_trans j5).
  have ne := nth_neq hp j0; have := adj_consecutive hp j0.
  have -> : (j == 1) || (0 == 0) && (j == (size (xv :: p)).-1) = false by rewrite sp; lia.
  by move: ne; case: (nth xv (xv :: p) j) => [i|[k|]].
have lt4 : 3 < 4 < size (xv :: p) by rewrite sp ltnSn ltnW.
by have := not_YY hp lt4; rewrite !Y // => /(_ isT isT).
Qed.

Lemma isYE d i : hole d -> 5 < size d -> i < size d -> isY (nth xv d i) = ~~ isC (nth xv d i).
Proof.
move=> hd d6 /(mem_nth xv); case: (nth xv d i) => [//|[//|]] xd.
by rewrite (negbTE (x_notin hd d6)) in xd.
Qed.

(** The vertices of a hole that are not consecutive to some [y_k] are on C. *)
Lemma far_from_Y d i : hole d -> 5 < size d -> isY (nth xv d 0) -> 1 < i < (size d).-1 ->
  isC (nth xv d i).
Proof.
move=> hd d6 y0 i1; apply: negbNE; rewrite -isYE //; first lia.
by apply: (not_YY hd _ _ y0); lia.
Qed.

(** The positions of consecutive vertices of C on a hole form a walk on C. *)
Lemma walk_hole d s m : hole d -> s + m <= size d ->
  (forall i, i < m -> isC (nth xv d (s + i))) -> walk n m (fun i => pos (nth xv d (s + i))).
Proof.
move=> hd sm cd; split=> [i|i lt_i|i lt_i]; first exact: pos_lt.
  rewrite -adj_CC ?cd ?(ltnW lt_i) // adj_consecutive ?addnS ?eqxx //.
  by rewrite -addnS leqnn (leq_trans _ sm) // ltn_add2l.
move=> /pos_inj e; have lt_s : s + i < s + i.+2 < size d.
  by rewrite ltn_add2l leqW //= (leq_trans _ sm) // ltn_add2l.
by have := nth_neq hd lt_s; rewrite e ?eqxx ?cd // ltnW // ltnW.
Qed.

(** A hole included in C has length at least [n]: it is C. *)
Lemma hole_CC d : hole d -> (forall i, i < size d -> isC (nth xv d i)) -> n <= size d.
Proof.
move=> hd cd; have [_ d4 _] := (hole_nthP xv d).1 hd.
have lt0 : 0 < (size d).-1 < size d by case: (size d) d4 => [|[|]] //= ? _; rewrite ltnSn.
have [_ s1] := andP lt0; have s0 := leq_ltn_trans (leq0n _) s1.
apply: (closed_walk (@walk_hole d 0 (size d) hd (leqnn _) cd)); first exact: ltnW.
by rewrite !add0n -adj_CC ?cd // adj_consecutive // !eqxx orbT.
Qed.

(** A path of C that forms, with the adjacent vertices [y_k] and [y_k'], a hole of length at least
    6 and less than [n]: the hole has length 2q + 2 if [k = k'] and q + 3 otherwise. *)
Lemma even_hole d m (k k' : 'I_3) : let v := nth xv d in
  hole d -> size d < n -> size d = m.+1 + (k != k') -> 3 < m ->
  (forall i, i < m -> isC (v i.+1)) -> v 0 = yv k ->
  yv k' -- v m -> ~~ (yv k' -- v m.-1) -> ~~ odd (size d).
Proof.
case: m => [|[|[|[|m]]]] // v hd lt_n em _ cm v0 vm vm1.
have sm : 1 + m.+4 <= size d by rewrite em leq_addr.
have m1 : 1 < m.+4 <= n by apply: ltnW (ltn_trans sm lt_n).
have e : m.+3 = if k == k' then 2 * q else q.
  apply: (walk_between_arcs (@walk_hole d 1 m.+4 hd sm cm) m1 (ltn_ord k) (ltn_ord k')) => //;
    rewrite -adj_YC ?cm // -/(v _) -v0 adj_consecutive //; lia.
by rewrite em oddD /=; move: e; case: eqVneq; lia.
Qed.

(** A hole of length at least 6 and less than [n], listed from some [y_k] followed by a vertex of
    C, has even length: its last vertex is on C, or is another [y_k']. *)
Lemma hole_Y d : hole d -> 5 < size d < n -> isY (nth xv d 0) -> isC (nth xv d 1) ->
  ~~ odd (size d).
Proof.
move=> hd /andP [d6 lt_n] y0 c1; have [k v0] := isY_yv y0.
have ci i : i < (size d).-2 -> isC (nth xv d i.+1).
  by case: i => [//|i] lt_i; apply: far_from_Y => //; lia.
have [cl|] := boolP (isC (nth xv d (size d).-1)).
  apply: (@even_hole d (size d).-1 k k); rewrite ?eqxx -?v0 ?adj_consecutive //; try lia.
  move=> i lt_i; have [lt_i2|ge_i] := ltnP i (size d).-2; first exact: ci.
  by have -> : i.+1 = (size d).-1 by lia.
rewrite -isYE // => [|/isY_yv [k' el]]; first lia.
have kk' : k != k'.
  have lt_l : 0 < (size d).-1 < size d by lia.
  by apply: contraNneq (nth_neq hd lt_l) => kk'; rewrite v0 el kk'.
by apply: (@even_hole d (size d).-2 k k'); rewrite ?kk' -?el 1?sg_sym ?adj_consecutive //; lia.
Qed.

(** An odd hole of length at least 6 and less than [n] contains no [y_k]: otherwise it can be
    listed as in [hole_Y]. *)
Lemma no_Y d i : hole d -> 5 < size d < n -> odd (size d) -> i < size d ->
  ~~ isY (nth xv d i).
Proof.
move=> hd d6n od /(mem_nth xv); move: (nth _ _ _) => u ud; apply: contraL od => y0.
have [p hp sp] := hole_mem_rot hd ud; rewrite -{d hd ud}sp in d6n *.
have [d6 lt_n] := andP d6n; have [c1|nc1] := boolP (isC (nth xv (u :: p) 1)).
  exact: hole_Y c1.
have lt j : j < 6 -> j < size (u :: p) by move=> j6; apply: leq_trans d6.
have y1 : isY (nth xv (u :: p) 1) by rewrite isYE ?lt.
have c2 : isC (nth xv (u :: p) 2) by apply: far_from_Y => //; apply: (lt 3).
rewrite -(size_rot 1); apply: hole_Y; rewrite ?size_rot ?nth_rot1 ?modn_small ?lt //.
exact: hole_rot.
Qed.

Lemma shortest_C : shortest_long_odd_hole 7 C.
Proof.
split=> [|d [hd od d7]]; first by split; [exact: hole_C|rewrite size_C; lia|rewrite size_C; lia].
rewrite size_C leqNgt; apply/negP => lt_n.
suff : n <= size d by rewrite leqNgt lt_n.
apply: hole_CC => // i lt_i; apply: negbNE; rewrite -(isYE hd (ltnW d7) lt_i).
by apply: no_Y; rewrite ?(ltnW d7).
Qed.

(** ** Major vertices and paths of C *)

Lemma pos_C : map pos C = iota 0 n.
Proof. by rewrite -map_comp -val_enum_ord; apply: eq_map. Qed.

(** A vertex with four consecutive neighbours on C is C-major. *)
Lemma major_C v a : a + 4 <= n -> v \notin C ->
  (forall u, isC u -> a <= pos u < a + 4 -> u -- v) -> major C v.
Proof.
move=> a4 vC adj; split=> // -[p [_ sp np]].
have us : uniq (take 4 (drop a C)).
  by rewrite take_uniq // drop_uniq //; have [] := (hole_nthP xv C).1 hole_C.
have : {subset take 4 (drop a C) <= p}.
  move=> u us'; have uC : u \in C := mem_drop (mem_take us').
  apply: np => //; apply: adj; first by rewrite -mem_C.
  by have := map_f pos us'; rewrite map_take map_drop pos_C drop_iota take_iota mem_iota; lia.
move/(uniq_leq_size us); rewrite size_take size_drop size_C sp; case: ifP; lia.
Qed.

Lemma major_yv k : major C (yv k).
Proof.
apply: (@major_C _ (k * q)); first by case: k => [[|[|[|]]]] //= _; lia.
  by rewrite mem_C.
by move=> u cu pu; rewrite sg_sym adj_YC // /inarc; lia.
Qed.

Lemma major_xv : major C xv.
Proof. by apply: (@major_C _ 0); [lia|rewrite mem_C|move=> [i|//]]. Qed.

(** A path of C with less than [q] edges has no vertex on some arc. *)
Lemma path_misses_arc p : cycle_path C p -> (size p).-1 < q ->
  exists k : 'I_3, forall u, u \in p -> ~~ (yv k -- u).
Proof.
move=> [i [m [lt_m ->]]]; rewrite size_C in lt_m.
rewrite size_take size_rot size_C => lt_q; have {lt_q} mq : m < q by case: ifP lt_q; lia.
wlog lt_i : i / i < n => [W|].
  have [/W //|le_i] := ltnP i n; rewrite rot_oversize ?size_C //.
  by have := W 0; rewrite rot0; apply; lia.
have [k lt_k miss] := interval_misses_arc lt_i mq; exists (Ordinal lt_k) => u up.
have cu : isC u by rewrite -mem_C; have := mem_take up; rewrite mem_rot.
rewrite adj_YC //; apply: miss; first exact: pos_lt.
have := map_f pos up; rewrite map_take map_rot pos_C /rot drop_iota take_iota take_cat size_iota.
by case: ifP => h; rewrite ?take_iota ?mem_cat !mem_iota; clear up; lia.
Qed.

End Counterexample.

(** With [q > b], the set M = {x, y_0, y_1, y_2} refutes the bound [b] for [ell = 7]. *)
Theorem disproof : ~ main.AX_long_odd_hole_heavy_path_lemma.
Proof.
move=> /(_ 7 isT) [b H].
have q4 : 4 < 2 * b + 5 by lia.
have oq : odd (2 * b + 5) by lia.
have [||p [cp sp np]] := H _ _ (~: [set u | isC u]) (shortest_C q4 oq).
- by case=> [i|[k|]]; rewrite !inE // => _; [apply: major_yv|apply: major_xv].
- by exists (xv _); [rewrite !inE|case=> [i|[k|]]; rewrite !inE].
have [|k miss] := path_misses_arc q4 oq cp; first by lia.
have [|u up] := np (yv _ k); first by rewrite !inE.
by apply/negP/miss.
Qed.
