(** * Short properly coloured cycles imply the Caccetta-Häggkvist conjecture

Let D be a loopless digraph with n vertices and minimum out-degree at least r > 0.  If D has a
digon, it is a directed cycle of length 2 <= ⌈n/r⌉, since r < n.  Otherwise, colour each edge of
the underlying graph of D by its tail: each of the n colour classes has at least r edges.  The
conjecture on properly coloured cycles gives a cycle C of length at most ⌈n/r⌉ in which no vertex
is the tail of its two edges.  Hence an arc of C oriented backwards is followed by another one,
and C is a directed cycle of D in one of its two directions.

This is the remark following Conjecture 4 in DeVos et al. (arXiv:1806.00825), the edge e099 of
relations.json in graph-conjectures.  It was formalized in graph-theory-rocq
(atlas/theories/conjectures/implications_A2.v). *)

From GraphTheory Require Import digraph sgraph.
From mathcomp Require Import boot zify_ssreflect.
From GC.GraphLib Require Import misc digraph minor(next_next_neq).
From GC.cycle.AX_short_rainbow_cycles_proper_incident_edges Require Import
  main(AX_short_rainbow_cycles_proper_incident_edges).
From GC.digraph.OPG_caccetta_haggkvist_outdegree_short_cycle Require Import
  main(OPG_caccetta_haggkvist_outdegree_short_cycle).

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Abbreviation properly_coloured_cycle :=
  GC.cycle.AX_short_rainbow_cycles_proper_incident_edges.main.properly_coloured_cycle.

Section Colouring.
Variables (D : diGraph) (v0 : D).
Hypothesis oD : oriented D.

(** The tail of an edge [e] of the underlying graph ([v0] if [e] is not an edge). *)
Definition tail (e : {set D}) : D :=
  if [pick u in e | [exists w in e, u -- w]] is Some u then u else v0.

(** The colour of an edge is its tail. *)
Definition col (e : {set D}) : 'I_#|D| := enum_rank (tail e).

(** The tail of an arc. *)
Lemma tailE u w : u -- w -> tail [set u; w] = u.
Proof.
move=> uw; rewrite /tail; case: pickP => [x /andP[] | /(_ u)].
  case/set2P=> -> // /existsP[y /andP[/set2P[] -> wy]]; last by have := oD wy; rewrite wy.
  by have := oD uw; rewrite wy.
by rewrite set21 /= => /negbT/existsPn/(_ w); rewrite set22 uw.
Qed.

(** An oriented digraph has no loop. *)
Lemma no_loop (x : D) : ~~ (x -- x).
Proof. by apply/negP => xx; have := oD xx; rewrite xx. Qed.

(** Colour classes: the edges from a vertex to its out-neighbours. *)
Lemma col_classes r : min_outdeg_ge D r ->
  forall i, r <= #|[set e in E(underlying D) | col e == i]|.
Proof.
move=> deg i; set v := enum_val i; apply: leq_trans (deg v) _.
have inj : {in N(v) &, injective (fun w => [set v; w])}.
  move=> w w' _ vw' /setP /(_ w'); rewrite !inE eqxx orbT.
  by case/orP=> /eqP // vE; rewrite vE in_opn (negPf (no_loop v)) in vw'.
rewrite /outdeg -(card_in_imset inj); apply/subset_leq_card/subsetP => _ /imsetP[w vw ->].
rewrite in_opn in vw; rewrite inE in_edges /= /col tailE // enum_valK eqxx andbT.
rewrite [_ -- _]/edge_rel /= vw andbT; apply/eqP => vE.
by move: vw; rewrite -vE (negPf (no_loop v)).
Qed.

(** In a properly coloured cycle, all arcs have the same direction. *)
Lemma orient (c : seq D) :
  seq_cycle (@edge_rel (underlying D)) c -> @properly_coloured_cycle (underlying D) #|D| col c ->
  cycle (--) c \/ cycle (fun x y => y -- x) c.
Proof.
move=> /andP[/andP[cc uc] c3] pc.
have arc x : x \in c -> x -- next c x || next c x -- x.
  by move/(next_cycle cc); rewrite [_ -- _]/edge_rel /= => /andP[].
(* The edge from a vertex of [c] to its successor. *)
have edge x : x \in c -> [set x; next c x] \in seq_cycle_edge_list c.
  case/rot_to => i s e.
  rewrite -(perm_mem (perm_seq_cycle_edge_list_rot i c)) -(next_rot i uc) e.
  rewrite seq_cycle_edge_list_cons; case: s {e} => [|y t] /=; rewrite eqxx.
  1,2: by rewrite seq_edge_list_cons mem_head.
(* A backward arc is followed by a backward arc: otherwise, a vertex is the tail of its two
   edges. *)
have step x : x \in c -> next c x -- x -> next c (next c x) -- next c x.
  move=> xc yx; have yc : next c x \in c by rewrite mem_next.
  case/orP: (arc _ yc) => // yz; have := pc _ _ (edge x xc) (edge _ yc).
  rewrite /col [[set x; _]]setUC !tailE // eqxx => h; suff : false by []; apply: h.
    apply/eqP => /setP/(_ x); rewrite !inE eqxx orbT => /esym/orP[/eqP xy|/eqP xz].
      by move: yx; rewrite -xy (negPf (no_loop x)).
    by have := next_next_neq uc c3 xc; rewrite -xz eqxx.
  by rewrite -setI_eq0; apply/set0Pn; exists (next c x); rewrite !inE eqxx.
have [/existsP[x0 /andP[x0c b0]]|/existsPn fw] := boolP [exists x in c, next c x -- x].
  right; apply: (cycle_from_next uc) => y yc.
  have mi m : iter m (next c) x0 \in c by elim: m => //= m; rewrite mem_next.
  rewrite -(iter_findex (_ : fconnect (next c) x0 y)) ?(fconnect_cycle (cycle_next uc) x0c) //.
  by elim: findex => //= m; apply: step (mi m).
left; apply: (cycle_from_next uc) => y yc; case/orP: (arc y yc) => // b.
by have := fw y; rewrite yc b.
Qed.

End Colouring.

Theorem AX_short_rainbow_cycles_proper_incident_edges_implies_OPG_caccetta_haggkvist_outdegree_short_cycle :
  AX_short_rainbow_cycles_proper_incident_edges -> OPG_caccetta_haggkvist_outdegree_short_cycle.
Proof.
move=> HR D r n0 nl r0 deg.
have [/existsP[u /existsP[v /andP[uv vu]]]|/existsPn nd] :=
  boolP [exists u : D, exists v, u -- v && v -- u].
  exists [:: u; v]; split.
    apply/andP; split => //; rewrite /ucycleb /= uv vu !inE !andbT.
    by apply: contraTneq uv => ->; rewrite nl.
  have : #|N(u)| <= #|[set~ u]|.
    by apply/subset_leq_card/subsetP => w; rewrite in_opn !inE; apply: contraTneq => ->; rewrite nl.
  have : r <= #|N(u)| := deg u.
  rewrite cardsC1 leq_divRL //=; lia.
have oD : oriented D.
  by move=> x y xy; apply/negP => yx; have /existsPn/(_ y) := nd x; rewrite xy yx.
have [v0 _] := card_gt0P n0.
have [c [cyc [sc pc]]] := HR #|D| r (underlying D) (col v0) n0 r0 erefl (col_classes v0 oD deg).
have [/andP[_ uc] c3] := andP cyc.
have c0 : ~~ nilp c by rewrite /nilp -lt0n (ltnW (ltnW c3)).
case: (orient oD cyc pc) => [fw|bw]; [exists c | exists (rev c)]; rewrite ?size_rev; split => //.
  by apply/and3P; split.
by apply/and3P; split; rewrite ?rev_cycle ?rev_uniq // /nilp size_rev.
Qed.

Check (AX_short_rainbow_cycles_proper_incident_edges_implies_OPG_caccetta_haggkvist_outdegree_short_cycle :
  GC.cycle.AX_short_rainbow_cycles_proper_incident_edges.main.AX_short_rainbow_cycles_proper_incident_edges ->
  GC.digraph.OPG_caccetta_haggkvist_outdegree_short_cycle.main.OPG_caccetta_haggkvist_outdegree_short_cycle).
Print Assumptions AX_short_rainbow_cycles_proper_incident_edges_implies_OPG_caccetta_haggkvist_outdegree_short_cycle.
