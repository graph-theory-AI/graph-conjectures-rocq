(** * Even-hole-free graphs have no C_4, theta, prism or even wheel

Each of these configurations contains an even hole:
- the 4-cycle is an even hole;
- a theta is made of three paths between two vertices: two of them have lengths of the same
  parity, and their union is an even hole;
- a prism is made of three paths between two triangles: two of them have lengths of the same
  parity, and their union with two edges of the triangles is an even hole;
- if a vertex v outside an odd hole c has an even number k >= 4 of neighbours in c, these
  neighbours cut c into k arcs, whose lengths add up to the odd length of c: some arc has an
  odd number of inner vertices, and with v it is an even hole.

For thetas and prisms, the image of a hole of K in a subdivision H of K is a hole of H
(GraphLib/minor.v, [subdiv_hole]).

These results were formalized in graph-theory-rocq (minor-theory/theories/foundations/
hole_containments.v and minor-theory/theories/conjectures/implications_X42.v). *)

From GraphTheory Require Import preliminaries digraph sgraph.
From mathcomp Require Import boot.
From GC.GraphLib Require Import misc.
From GC.GraphLib Require minor.
From GC.minor.AX_c4_diamond_theta_prism_bounded_treewidth Require main.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Abbreviation cycle_graph := main.cycle_graph.
Abbreviation cartesian_product := main.cartesian_product.
Abbreviation subdivision_model := main.subdivision_model.
Abbreviation subdiv_path := main.subdiv_path.
Abbreviation subdiv_spans := main.subdiv_spans.
Abbreviation is_theta := main.is_theta.
Abbreviation prism_subdivision := main.prism_subdivision.
Abbreviation even_wheel_free := main.even_wheel_free.

(** ** The 4-cycle *)

Lemma cycle_graph_hole (n : nat) : 3 < n -> hole (enum 'I_n : seq (cycle_graph n)).
Proof.
move=> n3; have x0 : cycle_graph n := Ordinal (leq_trans (isT : 0 < 4) n3).
apply/(hole_nthP x0); rewrite size_enum_ord; split=> //; first exact: enum_uniq.
move=> a b la lb; have E k (lk : k < n) : nth x0 (enum 'I_n) k = Ordinal lk.
  by apply/val_inj; rewrite /= nth_enum_ord.
rewrite (E a la) (E b lb) /edge_rel /= -val_eqE /=; apply/andb_idl => h; apply/eqP => ab.
move: h lb; rewrite ab orbb leq_eqVlt => /eqP + /predU1P[e|lt].
  by rewrite -e modnn => b0; rewrite -e -b0 in n3.
by rewrite modn_small // => /eqP; rewrite eqn_leq ltnn.
Qed.

Lemma even_hole_free_C4 (G : sgraph) : even_hole_free G -> ~ has_induced_copy G (cycle_graph 4).
Proof.
move=> eh [i]; apply: (eh (map i (enum 'I_4))); first exact/minor.hole_isubgraph/cycle_graph_hole.
by rewrite size_map size_enum_ord.
Qed.

(** ** The image of a 4-cycle in a subdivision *)

Section FourCycle.
Variables (K H : sgraph) (m : subdivision_model K H).
Local Abbreviation P := (subdiv_path m).

(** A 4-cycle of [K] without diagonals gives a hole of length 4 plus the number of inner
    vertices of the four paths.  The subdivision models of main.v have the fields of those of
    GraphLib, whose lemma [subdiv_hole] applies to the copy [m'] of [m]. *)
Lemma four_cycle_hole (w0 w1 w2 w3 : K) : subdiv_spans m ->
  w0 -- w1 -> w1 -- w2 -> w2 -- w3 -> w3 -- w0 -> ~~ w0 -- w2 -> ~~ w1 -- w3 ->
  w0 != w2 -> w1 != w3 ->
  exists c : seq H, hole c /\
    size c = (size (P w0 w1) + size (P w1 w2) + size (P w2 w3) + size (P w3 w0)).+4.
Proof.
move=> sp e01 e12 e23 e30 n02 n13 d02 d13.
pose m' := minor.SubdivisionModel (@main.subdiv_branch_inj _ _ m) (@main.subdiv_pathP _ _ m)
  (@main.subdiv_pathC _ _ m) (@main.subdiv_path_branch _ _ m) (@main.subdiv_path_disjoint _ _ m).
have hK : hole [:: w0; w1; w2; w3].
  apply/(hole_nthP w0); split=> //.
    rewrite /= !inE !negb_or d02 d13 (sg_edgeNeq e01) (sg_edgeNeq e12) (sg_edgeNeq e23).
    by rewrite eq_sym (sg_edgeNeq e30).
  move=> [|[|[|[|i]]]] [|[|[|[|j]]]] //= _ _; rewrite ?sg_irrefl ?(sg_sym w1 w0) ?(sg_sym w2 w0)
    ?(sg_sym w2 w1) ?(sg_sym w3 w1) ?(sg_sym w3 w2) ?(sg_sym w0 w3)
    ?e01 ?e12 ?e23 ?e30 ?(negbTE n02) ?(negbTE n13) //.
exists (minor.subdiv_walk m' w0 [:: w1; w2; w3; w0]); split.
  exact: (@minor.subdiv_hole _ _ m' sp _ _ hK).
by rewrite minor.size_subdiv_walk /= addn0 !addnA.
Qed.

End FourCycle.

(** ** Thetas and prisms *)

(** Two of three booleans are equal. *)
Lemma two_equal (f : 'I_3 -> bool) : exists j k : 'I_3, j != k /\ f j = f k.
Proof.
pose o0 : 'I_3 := ord0; pose o1 : 'I_3 := Ordinal (isT : 1 < 3); pose o2 : 'I_3 := ord_max.
have [e|n01] := eqVneq (f o0) (f o1); first by exists o0, o1.
have [e|n02] := eqVneq (f o0) (f o2); first by exists o0, o2.
by exists o1, o2; split=> //; move: n01 n02; case: (f o0); case: (f o1); case: (f o2).
Qed.

Lemma theta_even_hole (H : sgraph) : is_theta H -> exists c : seq H, hole c /\ ~~ odd (size c).
Proof.
case=> m sp; pose a0 : KB 2 3 := inl ord0; pose a1 : KB 2 3 := inl ord_max.
have sz j : size (subdiv_path m a1 (inr j)) + size (subdiv_path m (inr j) a0)
          = size (subdiv_path m a0 (inr j)) + size (subdiv_path m (inr j) a1).
  rewrite addnC (@main.subdiv_pathC _ _ m (inr j) a1) // size_rev.
  by rewrite (@main.subdiv_pathC _ _ m a0 (inr j)) // size_rev.
have [j [k [jk ejk]]] :=
  two_equal (fun j => odd (size (subdiv_path m a0 (inr j)) + size (subdiv_path m (inr j) a1))).
have := @four_cycle_hole _ _ m a0 (inr j) a1 (inr k) sp isT isT isT isT isT isT isT jk.
by case=> c [hc sc]; exists c; rewrite sc /= -addnA sz oddD ejk addbb.
Qed.

Lemma prism_even_hole (H : sgraph) :
  prism_subdivision H -> exists c : seq H, hole c /\ ~~ odd (size c).
Proof.
case=> m [sp tri]; pose o : 'I_2 := ord0; pose l : 'I_2 := ord_max.
have e (j j' : 'I_3) (t t' : 'I_2) : (((j, t) : cartesian_product 'K_3 'K_2) -- (j', t')) =
  ((j == j') && (t != t')) || ((t == t') && (j != j')) by [].
have [i [i' [ii' eii']]] :=
  two_equal (fun i => odd (size (subdiv_path m ((i, o) : cartesian_product 'K_3 'K_2) (i, l)))).
have := @four_cycle_hole _ _ m (i, o) (i, l) (i', l) (i', o) sp.
rewrite !e !eqxx (eq_sym i') (negbTE ii') /= => /(_ isT isT isT isT isT isT).
rewrite !xpair_eqE !andbF => /(_ isT isT) [c [hc sc]]; exists c; rewrite sc.
rewrite (tri (i, l) (i', l)) ?(tri (i', o) (i, o)) ?e ?eqxx ?(eq_sym i') ?ii' ?orbT //.
rewrite (@main.subdiv_pathC _ _ m (i', o) (i', l)) ?e ?eqxx //= size_rev !addn0.
by rewrite oddD eii' addbb.
Qed.

Lemma even_hole_free_theta (G H : sgraph) :
  even_hole_free G -> is_theta H -> ~ has_induced_copy G H.
Proof.
move=> eh /theta_even_hole[c [hc ec]] [i]; apply: (eh (map i c)); first exact: minor.hole_isubgraph.
by rewrite size_map.
Qed.

Lemma even_hole_free_prism (G H : sgraph) :
  even_hole_free G -> prism_subdivision H -> ~ has_induced_copy G H.
Proof.
move=> eh /prism_even_hole[c [hc ec]] [i]; apply: (eh (map i c)); first exact: minor.hole_isubgraph.
by rewrite size_map.
Qed.

(** ** Even wheels *)

(** A sequence [s] followed by an element [x] of [S], with an odd number of elements not in [S],
    has a maximal run [q] of elements not in [S] of odd length, preceded by an element of [S] or
    by nothing, and followed by an element [y] of [S]. *)
Lemma odd_gap (T : eqType) (S : pred T) (x : T) (s : seq T) :
  S x -> odd (count (predC S) s) ->
  exists u q y w, [/\ rcons s x = u ++ q ++ y :: w, S (last x u), all (predC S) q, S y
                    & odd (size q)].
Proof.
move=> Sx; have [n] := ubnP (size s); elim: n s => // n IH s.
have [/split_find[y q w Sy qS]|hs] := boolP (has S s); last first.
  move=> _ os; exists [::], s, x, [::]; rewrite cats1 all_predC hs; split=> //.
  by have /eqP <- : count (predC S) s == size s by rewrite -all_count all_predC.
have cq : count (predC S) q = size q by apply/eqP; rewrite -all_count all_predC.
rewrite size_cat size_rcons -cats1 -catA count_cat cq /= Sy /= add0n oddD => lt.
have [oq _|oq /= ow] := boolP (odd (size q)).
  by exists [::], q, y, (rcons w x); rewrite rcons_cat all_predC qS.
have [|u [q' [y' [w' [E Su qS' Sy' oq']]]]] := IH w _ ow.
  by rewrite -ltnS; apply: leq_ltn_trans lt; rewrite addSn ltnS leq_addl.
exists (rcons q y ++ u), q', y', w'; split=> //.
  by rewrite rcons_cat rcons_cons E -catA cat_rcons.
by rewrite last_cat last_rcons; case: u {E} Su.
Qed.

(** An edge of the path [y :: r ++ [:: x]] with [r] nonempty has an end in [r]. *)
Lemma edge_inner (T : finType) (y x : T) (r : seq T) (e : {set T}) :
  r != [::] -> e \in seq_edge_list (y :: rcons r x) -> exists2 z, z \in r & z \in e.
Proof.
elim: r y => [//|z r IH] y _; rewrite rcons_cons seq_edge_list_cons inE.
case/predU1P => [->|]; first by exists z; rewrite ?mem_head ?set22.
case: r IH => [|z' r] IH; first by rewrite /= inE => /eqP->; exists z; rewrite ?mem_head ?set21.
by case/IH => // u ur ue; exists u; rewrite // inE ur orbT.
Qed.

(** A vertex [v] outside a hole [x :: q ++ y :: r], adjacent to [x] and [y] and to no vertex of
    [q], with [q] and [r] nonempty, forms with [x :: q ++ [:: y]] a hole. *)
Lemma arc_hole (G : sgraph) (v x y : G) (q r : seq G) :
  hole (x :: q ++ y :: r) -> v \notin x :: q ++ y :: r -> v -- x -> v -- y ->
  {in q, forall u, ~~ v -- u} -> q != [::] -> r != [::] -> hole (v :: x :: rcons q y).
Proof.
move=> [[/andP[/andP[cyc uc] _] ch] _] vc vx vy vq q0 r0.
have cE : x :: q ++ y :: r = (x :: rcons q y) ++ r by rewrite cat_cons cat_rcons.
have pA : path (--) x (rcons q y) by move: cyc; rewrite cE /= rcons_cat cat_path => /andP[].
rewrite cE in uc vc ch; move: uc; rewrite cat_uniq => /and3P[uA /hasPn Ar _].
have vA : v \notin x :: rcons q y by move: vc; rewrite mem_cat negb_or => /andP[].
split; last by rewrite /= size_rcons; case: (q) q0.
have EA : seq_cycle_edge_list (v :: x :: rcons q y) =
    [set v; x] :: rcons (seq_edge_list (x :: rcons q y)) [set y; v].
  by rewrite seq_cycle_edge_list_cons rcons_cons seq_edge_list_cons
    (seq_edge_list_rcons x (rcons q y) v) last_rcons.
split; first by rewrite /seq_cycle /ucycleb /= rcons_path last_rcons pA vx sg_sym vy vA
  -cons_uniq uA size_rcons.
have memA z : z \in x :: rcons q y -> [|| z == x, z == y | z \in q].
  by rewrite in_cons mem_rcons in_cons.
move=> a b; rewrite EA in_cons => /predU1P[->|aA] /predU1P[->|bA] ab.
- by rewrite sg_irrefl in ab.
- case/or3P: (memA b bA) => [/eqP->|/eqP->|bq]; first by rewrite mem_head.
    by rewrite in_cons mem_rcons setUC mem_head orbT.
  by rewrite (negbTE (vq b bq)) in ab.
- case/or3P: (memA a aA) => [/eqP->|/eqP->|aq]; first by rewrite setUC mem_head.
    by rewrite in_cons mem_rcons mem_head orbT.
  by rewrite sg_sym (negbTE (vq a aq)) in ab.
move: (ch a b); rewrite !mem_cat.
move=> /(_ (introT orP (or_introl aA)) (introT orP (or_introl bA)) ab).
rewrite -cE seq_cycle_edge_list_cat mem_cat => /orP[e|/(edge_inner r0)[z zr /set2P[] za]].
- by rewrite in_cons mem_rcons in_cons e !orbT.
- by case/negP: (Ar z zr); rewrite za; exact: aA.
- by case/negP: (Ar z zr); rewrite za; exact: bA.
Qed.

Lemma even_hole_free_even_wheel (G : sgraph) : even_hole_free G -> even_wheel_free G.
Proof.
move=> eh v c hc vc; pose S := [pred u | v -- u].
have uc : uniq c by case: hc => [[/andP[/andP[_ ->]]]].
have -> : #|N(v) :&: [set:: c]| = count S c.
  rewrite -size_filter -(card_uniqP (filter_uniq S uc)).
  by apply: eq_card => u; rewrite !inE mem_filter.
move=> c3; apply/negPn/negP => ec.
have oc : odd (size c) by apply/negPn/negP => /(eh c hc).
have /hasP[x xc Sx] : has S c by rewrite has_count (leq_trans _ c3).
(* the rotations of [c] *)
pose P t := [/\ hole t, v \notin t & perm_eq t c].
have Prot n t : P t -> P (rot n t).
  by case=> ht vt pt; split; [exact: hole_rot | rewrite mem_rot | rewrite perm_rot].
have [i s E] := rot_to xc.
have Pxs : P (x :: s) by rewrite -E; apply: Prot; split; rewrite ?perm_refl.
have os : odd (count (predC S) s).
  case: Pxs => _ _ /[dup] /permP cS /perm_size sS.
  have := count_predC S s; move/(congr1 odd); rewrite oddD.
  have cs : odd (count S s) by move: ec; rewrite -(cS S) /= (Sx : v -- x) add1n /= negbK.
  have ss : ~~ odd (size s) by move: oc; rewrite -sS.
  by rewrite cs (negbTE ss); case: odd.
(* an arc between two neighbours of [v] with an odd number of inner vertices *)
have [u [q [y [w [E1 Sx' qS Sy oq]]]]] := odd_gap Sx os.
have cq : count S q = 0 by apply/eqP; rewrite -leqn0 leqNgt -has_count -all_predC.
have [x' [r [Sx'' Pt]]] : exists x' r, S x' /\ P (x' :: q ++ y :: r).
  case/lastP: u E1 Sx' => [|u0 x'] /= E1 Sx'; last first.
    exists x', (w ++ u0); split; first by rewrite last_rcons in Sx'.
    have -> : x' :: q ++ y :: w ++ u0 = rot (size u0) (rot 1 (x :: s)).
      by rewrite rot1_cons E1 cat_rcons rot_size_cat cat_cons -catA.
    exact: (Prot _ _ (Prot _ _ Pxs)).
  case/lastP: w E1 => [|r z]; rewrite ?cats1 -?rcons_cons -?rcons_cat => /rcons_inj[sE _].
    by exfalso; case: Pxs => _ _ /permP/(_ S); rewrite sE /= Sx' cq => cS; rewrite -cS in c3.
  by exists x, r; split=> //; rewrite -sE.
case: Pt => ht vt /permP/(_ S) cS.
have r0 : r != [::].
  apply: contraTneq c3 => r0.
  by rewrite -cS r0 /= count_cat cq /= (Sx'' : v -- x') (Sy : v -- y).
apply: (eh _ (arc_hole ht vt Sx'' Sy _ _ r0)); first by move=> z /(allP qS).
  by case: (q) oq.
by rewrite /= size_rcons /= oq.
Qed.
