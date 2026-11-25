(** * The graph of the triakis tetrahedron

This graph is obtained from the tetrahedron K4 by adding one vertex in each of its four faces.  It
is 3-connected, its induced cycles are triangles, and the four triangles of the tetrahedron are not
peripheral. *)

From GraphTheory Require Import preliminaries digraph sgraph connectivity.
From GC.GraphLib Require Import misc.
From GC.extremal.OPG_3_connected_geodesic_cycles_peripheral_lengths Require main.
From mathcomp Require Import boot order algebra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Abbreviation peripheral_cycle := main.peripheral_cycle.

(** The vertices are the [b i = (false, i)], which form the K4, and the [s i = (true, i)], where
    [s i] is adjacent to the [b j] with [j != i]. *)
Definition tt_rel (x y : bool * 'I_4) : bool := (x.2 != y.2) && ~~ (x.1 && y.1).

Lemma tt_sym : symmetric tt_rel.
Proof. by move=> x y; rewrite /tt_rel eq_sym [x.1 && _]andbC. Qed.

Lemma tt_irrefl : irreflexive tt_rel.
Proof. by move=> x; rewrite /tt_rel eqxx. Qed.

Definition TT : sgraph := SGraph tt_sym tt_irrefl.

Definition b (i : 'I_4) : TT := (false, i).
Definition s (i : 'I_4) : TT := (true, i).

Lemma ttE (x y : TT) : x -- y = (x.2 != y.2) && ~~ (x.1 && y.1).
Proof. by []. Qed.

(** ** 3-connectedness *)

(** At most two vertices do not separate TT: some [b i] remains, and it is joined to the other
    remaining vertices by an edge or, for [s i], by a path through another [b k]. *)
Lemma tt_3connected : 3.-connected TT.
Proof.
split=> [|S [x [y [xS yS sep]]]]; first by rewrite card_prod card_bool card_ord.
rewrite leqNgt; apply/negP => ltS.
have free i : exists2 j, j != i & b j \notin S.
  have /subsetPn[_ /imsetP[j ji ->] jS] : ~~ ([set b j | j in [set~ i]] \subset S).
    apply: contraL ltS => /subset_leq_card.
    by rewrite -leqNgt card_imset ?cardsC1 ?card_ord // => j k [].
  by exists j; rewrite // !inE in ji.
have [i _ iS] := free ord0.
have adj j w : b j \notin S -> w \notin S -> w.2 != j ->
    connect (restrict [predC S] (--)) (b j) w.
  by move=> jS wS wj; apply: connect1; rewrite /= !inE jS wS ttE /= eq_sym wj.
have to_b z : z \notin S -> connect (restrict [predC S] (--)) (b i) z.
  case: z => a j zS; have [e|ji] := eqVneq j i; last exact: adj.
  subst j; case: a zS => zS; last exact: connect0.
  have [k ki kS] := free i.
  by apply: connect_trans (adj _ _ iS kS ki) (adj _ _ kS zS _); rewrite eq_sym.
have xy : connect (restrict [predC S] (--)) x y.
  by apply: connect_trans (to_b y yS); rewrite srestrict_sym to_b.
have x_y : x != y by apply: separatesNeq (And3 xS yS sep).
have [p _ /subsetP sub] := connect_irredRP x_y xy; have [z zp zS] := sep p.
by have := sub z zp; rewrite !inE zS.
Qed.

(** ** Induced cycles *)

(** The two neighbours in an induced cycle of one of its vertices, some [s i] if there is one, are in
    the K4, hence adjacent, and the cycle is a triangle. *)
Lemma tt_induced_cycle (c : seq TT) : chordless_cycle c ->
  exists n x j k, rot n c = [:: x; b j; b k].
Proof.
move=> ch; have [x xc hx] : exists2 x, x \in c & forall y, y \in c -> x -- y -> ~~ y.1.
  have [/hasP[[[] i] ic //= _]|cB] := boolP (has (fun x : TT => x.1) c).
    by exists (s i) => // y _; rewrite ttE => /andP[].
  case: c ch cB => [[]//|x c] _ cB; exists x => [|y yc _]; first exact: mem_head.
  by apply: contra cB => y1; apply/hasP; exists y.
have [n t e] := rot_to xc; exists n, x.
have {}hx y : y \in x :: t -> x -- y -> exists j, y = b j.
  by rewrite -e mem_rot => yc xy; case: y yc xy (hx y yc xy) => [[] j] //; exists j.
have := chordless_cycle_rot n ch; rewrite e => {}ch {n e c xc}.
case: ch => /andP[/andP[cyc uc]]; case: t hx cyc uc => [|y [|z t]] // hx cyc uc _ ch.
move: cyc; rewrite /= rcons_path => /and4P[xy _ _ lx].
have yC : y \in [:: x, y, z & t] by rewrite !inE eqxx orbT.
have lC : last z t \in [:: x, y, z & t] by rewrite 2!in_cons mem_last !orbT.
have [j ej] := hx y yC xy.
have [k ek] : exists k, last z t = b k by apply: hx lC _; rewrite sg_sym.
have yl : y -- last z t.
  have : y != last z t by apply: contraTneq uc => ->; rewrite /= mem_last !andbF.
  by rewrite ej ek ttE xpair_eqE /= andbT.
have {ch} := ch y _ yC lC yl; rewrite (last_nth x).
rewrite -[[set y; _]]/[set nth x [:: x, y, z & t] 1; nth x [:: x, y, z & t] (size t).+2].
rewrite seq_cycle_edge_list_nth //= modnn orbF.
case: t ek {uc hx lx yC lC yl} => [/= -> _|w t _]; last by rewrite modn_small.
by exists j, k; rewrite ej.
Qed.

(** ** The triangles of the K4 *)

Lemma K4_not_peripheral j k l : uniq [:: j; k; l] -> ~ peripheral_cycle [:: b j; b k; b l].
Proof.
move=> u [_ con]; have [i iN] := @ord_fresh 4 [:: j; k; l] isT.
have all4 t : t \in [:: i; j; k; l] by apply: ord_size_enum; rewrite //= iN.
have iC a : ((a, i) : TT) \in ~: [set x in [:: b j; b k; b l]].
  move: iN; rewrite !inE !negb_or !xpair_eqE => /and3P[/negPf-> /negPf-> /negPf->].
  by rewrite !andbF.
have /connectP[[|x p]] := con (s i) (b i) (iC _) (iC _); first by move=> _ [].
case/andP=> /andP[/andP[_]]; rewrite !inE !negb_or => /and3P[xj xk xl].
case: x xj xk xl => [[] t]; rewrite ttE /= ?andbF // /b !xpair_eqE /= andbT => tj tk tl it.
by have := all4 t; rewrite !inE eq_sym (negPf it) (negPf tj) (negPf tk) (negPf tl).
Qed.
