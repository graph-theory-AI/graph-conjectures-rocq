(** * Even subgraphs: decomposition into cycles (Veblen) and balanced orientations

The edge set of an even subgraph of a multigraph is partitioned by cycles
([even_cycle_decomposition], Veblen's theorem).  The cycles are extracted one by one: a nonempty
set of edges without vertex of degree one contains a cycle ([has_circuit]), because a path in it
that cannot be extended ends at a vertex with a second edge, whose other end is on the path and
closes a cycle.  An even subgraph also has a balanced orientation, obtained by following closed
trails ([even_balanced_orientation]). *)

From GraphTheory Require Import mgraph.
From mathcomp Require Import boot.
From GC.GraphLib Require Import misc cycle.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Cycles in sets of edges *)

Section Veblen.
Variable G : mgraph.
Implicit Types (C D : {set edge G}) (v x y z : G).

(** A step [a] goes along the edge [a.1] from [stail a] to [shead a] (from the target of the edge
    when [a.2] is [true]).  A route from [x] is a sequence of consecutive steps. *)
Definition stail (a : edge G * bool) : G := endpoint a.2 a.1.
Definition shead (a : edge G * bool) : G := endpoint (~~ a.2) a.1.

Fixpoint route x (r : seq (edge G * bool)) : bool :=
  if r is a :: r' then (stail a == x) && route (shead a) r' else true.

Definition rlast x (r : seq (edge G * bool)) : G := last x (map shead r).

(** The set of the edges of [r]. *)
Definition redges (r : seq (edge G * bool)) : {set edge G} := [set e in map fst r].

Lemma route_cat x r1 r2 : route x (r1 ++ r2) = route x r1 && route (rlast x r1) r2.
Proof. by elim: r1 x => //= a r1 IH x; rewrite IH andbA. Qed.

Lemma route_uwalk x r : route x r -> uwalk x (rlast x r) (map fst r).
Proof.
elim: r x => [x _|[e b] r IH x /= /andP[/eqP <- /IH]]; first by rewrite /= eqxx.
by case: b; rewrite /rlast /stail /shead /= eqxx => ->; rewrite ?orbT.
Qed.

(** The tails of a route are its start followed by all heads but the last one. *)
Lemma route_tails x r : route x r -> rcons (map stail r) (rlast x r) = x :: map shead r.
Proof. by elim: r x => //= a r IH x /andP[/eqP -> /IH <-]. Qed.

(** Every vertex of a route ends a prefix of it. *)
Lemma route_prefix x z r :
  z \in x :: map shead r -> exists r1 r2, r = r1 ++ r2 /\ rlast x r1 = z.
Proof.
rewrite in_cons => /predU1P[->|/mapP[a /splitPr[r1 r2] ->]]; first by exists [::], r.
by exists (rcons r1 a), r2; rewrite cat_rcons /rlast map_rcons last_rcons.
Qed.

(** The degrees in the set of the edges of a route without repeated edge. *)
Lemma mdeg_in_redges r v : uniq (map fst r) ->
  mdeg_in (redges r) v = count (fun a => stail a == v) r + count (fun a => shead a == v) r.
Proof.
move=> ur; rewrite mdeg_inE.
have -> : \sum_(e in redges r) ((source e == v) + (target e == v))
          = \sum_(e <- map fst r) ((source e == v) + (target e == v)).
  by rewrite big_uniq //; apply: eq_bigl => e; rewrite inE.
rewrite big_map {ur}; elim: r => [|[e b] r IH]; first by rewrite big_nil.
rewrite big_cons IH /stail /shead; case: b => /=; last by rewrite addnACA.
by rewrite [(source e == v) + _]addnC addnACA.
Qed.

(** A closed route with distinct edges and distinct vertices is a cycle. *)
Lemma closed_route_circuit x r :
  r != [::] -> route x r -> rlast x r = x -> uniq (map fst r) -> uniq (map shead r) ->
  is_circuit (redges r).
Proof.
move=> rn0 hr hx ue uh; have tl := route_tails hr; rewrite hx in tl.
have verts u : subgraph_incident (redges r) u -> u \in x :: map shead r.
  case/existsP => e /andP[]; rewrite [e \in _]inE => /mapP[[f b] ar ->] /existsP[c /eqP <-].
  have [-> | ->] : endpoint c f = stail (f, b) \/ endpoint c f = shead (f, b).
    by case: b c {ar} => -[]; [left | right | right | left].
  - by rewrite -tl mem_rcons in_cons (map_f _ ar) orbT.
  - by rewrite in_cons (map_f _ ar) orbT.
split.
- by case: r rn0 {hr hx ue uh tl verts} => // a r _; apply/set0Pn; exists a.1; rewrite !inE eqxx.
- move=> v; rewrite mdeg_in_redges //.
  have -> : count (fun a => stail a == v) r = count (fun a => shead a == v) r.
    have := congr1 (count (pred1 v)) tl; rewrite -cats1 count_cat /= addn0 !count_map addnC.
    exact: addnI.
  have := count_uniq_mem v uh; rewrite count_map => ->.
  by case: (v \in _); [right | left].
- move=> u u' /verts /route_prefix[r1 [r2 [er <-]]] /verts /route_prefix[s1 [s2 [es <-]]].
  have /route_uwalk h1 : route x r1 by move: hr; rewrite er route_cat => /andP[].
  have /route_uwalk h2 : route x s1 by move: hr; rewrite es route_cat => /andP[].
  exists (rev (map fst r1) ++ map fst s1); rewrite /uwalk_in (uwalk_cat (uwalk_rev h1) h2).
  apply/allP => e; rewrite mem_cat mem_rev inE.
  by case/orP => h; [rewrite er | rewrite es]; rewrite map_cat mem_cat h.
Qed.

Lemma rlast_cat x r1 r2 : rlast x (r1 ++ r2) = rlast (rlast x r1) r2.
Proof. by rewrite /rlast map_cat last_cat. Qed.

(** A path in [C] from [x]: a route with edges in [C] and distinct vertices. *)
Definition spath C x r : bool :=
  [&& route x r, all (fun a => a.1 \in C) r, uniq (map fst r) & uniq (x :: map shead r)].

(** A path in [C] whose last vertex has another edge in [C] extends, or closes a cycle. *)
Lemma spath_step C x r f b :
  spath C x r -> f \in C -> f \notin map fst r -> endpoint b f = rlast x r ->
  (exists2 D : {set edge G}, D \subset C & is_circuit D) \/ (exists a, spath C x (rcons r a)).
Proof.
move=> /and4P[hr aC ue uv] fC fr hb.
case: (boolP (shead (f, b) \in x :: map shead r)) => [zin|znot]; last first.
  right; exists (f, b); apply/and4P; split.
  - by rewrite -cats1 route_cat hr /= /stail hb eqxx.
  - by rewrite all_rcons fC.
  - by rewrite map_rcons rcons_uniq fr.
  - by rewrite map_rcons -rcons_cons rcons_uniq znot.
left; have [r1 [r2 [er hz]]] := route_prefix zin.
exists (redges (r2 ++ [:: (f, b)])).
  apply/subsetP => e; rewrite inE map_cat mem_cat => /orP[/mapP[a ar ->]|].
    by apply: (allP aC); rewrite er mem_cat ar orbT.
  by rewrite inE => /eqP ->.
move: hr uv ue fr; rewrite er route_cat !map_cat -cat_cons !cat_uniq mem_cat negb_or.
move=> /andP[_ hr2] /and3P[_ hn u2] /and3P[_ _ ue2] /andP[_ fr2].
apply: (@closed_route_circuit (rlast x r1)).
- by rewrite cats1 -size_eq0 size_rcons.
- by rewrite route_cat hr2 /= -rlast_cat -er /stail hb eqxx.
- by rewrite rlast_cat /= hz.
- by rewrite map_cat cats1 rcons_uniq ue2 fr2.
- rewrite map_cat cats1 rcons_uniq u2 andbT /= -hz; apply: contra hn => h.
  by apply/hasP; exists (rlast x r1) => //; rewrite /rlast mem_last.
Qed.

(** The last vertex of a nonempty path has degree one in it. *)
Lemma spath_last C x r : spath C x r -> r != [::] -> mdeg_in (redges r) (rlast x r) = 1.
Proof.
case/and4P => hr _ ue uv rn0; rewrite mdeg_in_redges //.
have := uv; rewrite -(route_tails hr) rcons_uniq => /andP[ynot _].
have -> : count (fun a => stail a == rlast x r) r = count (pred1 (rlast x r)) (map stail r).
  by rewrite count_map.
have -> : count (fun a => shead a == rlast x r) r = count (pred1 (rlast x r)) (map shead r).
  by rewrite count_map.
move: uv => /andP[_ uh]; rewrite (count_uniq_mem _ uh) (count_memPn ynot) /rlast.
by case: r rn0 {hr ue ynot uh} => // a r _; rewrite /= mem_last.
Qed.

(** A nonempty set of edges without vertex of degree one contains a cycle. *)
Theorem has_circuit C :
  C != set0 -> (forall v, mdeg_in C v != 1) -> exists2 D : {set edge G}, D \subset C & is_circuit D.
Proof.
case/set0Pn => e0 e0C deg1.
suff ind n x r : spath C x r -> #|G| <= size r + n ->
    (r = [::] -> exists b, endpoint b e0 = x) ->
    exists2 D : {set edge G}, D \subset C & is_circuit D.
  by apply: (ind #|G| (source e0) [::]) => //; exists false.
elim: n x r => [|n IH] x r sp hn hr.
  case/and4P: sp => _ _ _ /card_uniqP; move: (max_card (mem (x :: map shead r))) => h hc.
  by move: (leq_trans h hn); rewrite hc /= size_map addn0 ltnn.
(* an edge of [C] at the end of the path, not in the path *)
have [f fC [fr [b hb]]] :
    exists2 f, f \in C & f \notin map fst r /\ exists b, endpoint b f = rlast x r.
  case: (eqVneq r [::]) => [r0 | rn0].
    by have [b hb] := hr r0; exists e0 => //; rewrite r0; split => //; exists b.
  have rC : redges r \subset C.
    by case/and4P: sp => _ /allP aC _ _; apply/subsetP => e; rewrite inE => /mapP[a /aC ? ->].
  have := deg1 (rlast x r); rewrite (mdeg_in_setD _ rC) (spath_last sp rn0).
  rewrite -[1]addn0 eqn_add2l -lt0n /mdeg_in addn_gt0.
  by case/orP => /card_gt0P[f]; rewrite !inE => /andP[/andP[fr fC] /eqP hf];
    exists f => //; split => //; [exists false | exists true].
have [//|[a spa]] := spath_step sp fC fr hb.
apply: (IH x (rcons r a) spa); first by rewrite size_rcons addSnnS.
by case: r {sp hn hr fr hb spa}.
Qed.

(** Veblen's theorem: the edge set of an even subgraph is partitioned by cycles. *)
Theorem even_cycle_decomposition C :
  even_subgraph C -> exists D : seq {set edge G}, cycle_decomposition_of C D.
Proof.
elim: {C}_.+1 {-2}C (ltnSn #|C|) => // n IH C hn Ce.
have [->|Cn0] := eqVneq C set0; first by exists [::]; split => // e; rewrite inE.
have [D DC [Dn0 Dreg Dcon]] : exists2 D : {set edge G}, D \subset C & is_circuit D.
  by apply: has_circuit Cn0 _ => v; apply: contraNneq (Ce v) => ->.
have lt : #|C :\: D| < n.
  rewrite -ltnS; apply: leq_trans hn; rewrite ltnS -(cardsID D C) (setIidPr DC) -addn1.
  by rewrite addnC leq_add2r card_gt0.
have [L [Lc Ln]] : exists L, cycle_decomposition_of (C :\: D) L.
  by apply: IH lt _ => v; have := Ce v; rewrite (mdeg_in_setD _ DC) oddD; case: (Dreg v) => ->.
exists (D :: L); split => [X /predU1P[->|/Lc] //|e]; rewrite /= Ln !inE.
by case: (boolP (e \in D)) => // /(subsetP DC) ->.
Qed.

(** A list of even subgraphs is refined into a list of cycles: each edge is in as many members of
    both lists. *)
Corollary even_subgraphs_cycles (L : seq {set edge G}) :
  (forall C, C \in L -> even_subgraph C) ->
  exists M : seq {set edge G}, (forall X, X \in M -> is_circuit X) /\
    forall e : edge G, count (fun X : {set edge G} => e \in X) M = count (fun C => e \in C) L.
Proof.
elim: L => [|C L IH] Le; first by exists [::].
have [D [Dc Dn]] := even_cycle_decomposition (Le C (mem_head C L)).
have [|M [Mc Mn]] := IH; first by move=> X XL; apply: Le; rewrite in_cons XL orbT.
exists (D ++ M); split => [X|e]; first by rewrite mem_cat => /orP[/Dc|/Mc].
by rewrite count_cat Dn Mn.
Qed.

End Veblen.

(** ** Balanced orientations of even subgraphs *)

Section Orientations.
Variable G : mgraph.
Implicit Types (C D : {set edge G}) (o : edge G -> bool) (x v : G) (r s : seq (edge G * bool)).

(** Along a route from [x], each vertex is left as often as it is entered, except for the two
    ends. *)
Lemma route_count x r v : route x r ->
  count (fun a => stail a == v) r + (rlast x r == v) = (x == v) + count (fun a => shead a == v) r.
Proof.
by move/route_tails/(congr1 (count (pred1 v))); rewrite -cats1 count_cat /= addn0 !count_map.
Qed.

Lemma closed_route_count x r v : route x r -> rlast x r = x ->
  count (fun a => stail a == v) r = count (fun a => shead a == v) r.
Proof. by move=> hr hx; have := route_count v hr; rewrite hx addnC => /addnI. Qed.

(** A trail in [C] from [x]: a route without repeated edge, with its edges in [C]. *)
Definition trail C x r := [&& route x r, uniq (map fst r) & all (fun a => a.1 \in C) r].

Lemma trail_size C x r : trail C x r -> size r <= #|C|.
Proof.
case/and3P => _ ur /allP rC; rewrite -(size_map fst) -(card_uniqP ur).
by apply/subset_leq_card/subsetP => e /mapP[a /rC + ->].
Qed.

(** A trail in an even subgraph that does not return to its start can be extended. *)
Lemma trail_step C x r : even_subgraph C -> trail C x r -> rlast x r != x ->
  exists a, trail C x (rcons r a).
Proof.
move=> Ce /and3P[hr ur rC] yx; set y := rlast x r in yx.
have rsub : redges r \subset C.
  by apply/subsetP => e; rewrite inE => /mapP[a /(allP rC) + ->].
have : odd (mdeg_in (C :\: redges r) y).
  move: (Ce y) (route_count y hr); rewrite (mdeg_in_setD _ rsub) mdeg_in_redges // eqxx.
  rewrite eq_sym (negbTE yx) add0n addn1 => h e; move: h.
  by rewrite -e addnS oddD /= addnn odd_double negbK.
move=> /odd_gt0; rewrite addn_gt0.
case/orP => /card_gt0P[f]; rewrite !inE => /andP[/andP[fr fC] /eqP fy];
  [exists (f, false) | exists (f, true)]; rewrite /trail -cats1 route_cat hr /= /stail fy eqxx;
  by rewrite map_cat cat_uniq ur /= orbF fr all_cat rC /= fC.
Qed.

(** Every trail in an even subgraph extends into a closed trail. *)
Lemma closed_trail C x r : even_subgraph C -> trail C x r ->
  exists r', trail C x (r ++ r') /\ rlast x (r ++ r') = x.
Proof.
move=> Ce; move: {2}(#|C| - size r) (leqnn (#|C| - size r)) => n.
elim: n r => [|n IH] r hn tr; have [e|yx] := eqVneq (rlast x r) x;
  try by exists [::]; rewrite cats0.
all: have [a tra] := trail_step Ce tr yx; have := trail_size tra; rewrite size_rcons.
  by rewrite leqn0 subn_eq0 in hn => /leq_trans/(_ hn); rewrite ltnn.
move=> _; have [|r2 [tr2 l2]] := IH (rcons r a) _ tra; last by exists (a :: r2); rewrite -cat_rcons.
by rewrite size_rcons subnS -subn1 leq_subLR add1n.
Qed.

(** Orienting the edges of a closed trail along it is balanced. *)
Lemma closed_trail_balanced C x s : trail C x s -> rlast x s = x ->
  balanced_orientation (redges s) (fun e => (e, false) \in s).
Proof.
case/and3P => hs us _ hx v; set o := (fun e => (e, false) \in s).
have dir a : a \in s -> orient_tail o a.1 = stail a /\ orient_head o a.1 = shead a.
  case: a => e [] es; rewrite /orient_tail /orient_head /o /stail /shead /=; last by rewrite es.
  suff -> : ((e, false) \in s) = false by [].
  move: es us => /splitPr[s1 s2]; rewrite map_cat cat_uniq /= mem_cat in_cons xpair_eqE andbF.
  case/and4P => _ /norP[n1 _] n2 _.
  by apply/negP => /orP[] /(map_f fst); [apply/negP | apply/negP].
have card (F : edge G -> G) (g : edge G * bool -> G) : {in s, forall a, F a.1 = g a} ->
    #|[set e in redges s | F e == v]| = count (fun a => g a == v) s.
  move=> hF; rewrite -(eq_in_count (a1 := fun a => F a.1 == v)); first by move=> a /hF /= ->.
  rewrite -(count_map fst (fun e => F e == v)) -size_filter -(card_uniqP (filter_uniq _ us)).
  by apply: eq_card => e; rewrite !inE mem_filter andbC.
rewrite (card _ (@stail G)) => [a /dir[] //|]; rewrite (card _ (@shead G)) => [a /dir[] //|].
exact: closed_route_count v hs hx.
Qed.

Lemma eq_balanced C o o' : {in C, o =1 o'} ->
  balanced_orientation C o -> balanced_orientation C o'.
Proof.
move=> oo' b v.
have -> : [set e in C | orient_tail o' e == v] = [set e in C | orient_tail o e == v].
  by apply/setP => e; rewrite !inE /orient_tail; case eC: (e \in C); rewrite //= oo'.
have -> : [set e in C | orient_head o' e == v] = [set e in C | orient_head o e == v].
  by apply/setP => e; rewrite !inE /orient_head; case eC: (e \in C); rewrite //= oo'.
exact: b.
Qed.

Lemma balanced_setD C D o : D \subset C ->
  balanced_orientation D o -> balanced_orientation (C :\: D) o -> balanced_orientation C o.
Proof.
move=> DC bD bCD v; have sp F : #|[set e in C | F e == v]|
    = #|[set e in D | F e == v]| + #|[set e in C :\: D | F e == v]|.
  rewrite -(cardsID D [set e in C | F e == v]); congr (_ + _); apply: eq_card => e; rewrite !inE.
    by case eD: (e \in D); rewrite ?andbF // (subsetP DC e eD) andbT.
  by rewrite andbA.
by rewrite !sp bD bCD.
Qed.

(** Every even subgraph has a balanced orientation. *)
Theorem even_balanced_orientation C : even_subgraph C -> exists o, balanced_orientation C o.
Proof.
elim: {C}_.+1 {-2}C (ltnSn #|C|) => // n IH C hn Ce.
have [->|/set0Pn[e eC]] := eqVneq C set0.
  by exists xpredT => v; apply: eq_card => e; rewrite !inE.
have [|r [tr hx]] := @closed_trail C (source e) [:: (e, false)] Ce.
  by rewrite /trail /= /stail eqxx eC.
set s := _ ++ r in tr hx; have /and3P[hs us sC] := tr.
have DC : redges s \subset C by apply/subsetP => f; rewrite inE => /mapP[a /(allP sC) + ->].
have [o2 bo2] : exists o, balanced_orientation (C :\: redges s) o.
  apply: IH => [|v].
    rewrite -ltnS (leq_trans _ hn) // ltnS -(cardsID (redges s) C) (setIidPr DC).
    by rewrite -addn1 addnC leq_add2r card_gt0; apply/set0Pn; exists e; rewrite inE mem_head.
  have := Ce v; rewrite (mdeg_in_setD _ DC) oddD mdeg_in_redges // (closed_route_count _ hs hx).
  by rewrite addnn odd_double.
exists (fun f => if f \in redges s then (f, false) \in s else o2 f).
apply: balanced_setD DC _ _; first by apply: eq_balanced (closed_trail_balanced tr hx) => f ->.
by apply: eq_balanced bo2 => f; rewrite inE => /andP[/negbTE ->].
Qed.

End Orientations.
