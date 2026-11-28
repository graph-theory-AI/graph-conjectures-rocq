(** * The subset deficit of a minimal counterexample

Lemma 2.2 of the paper of OpenAI (an adaptation of Lemma 4 of Seacrest, "The arc-weighted
version of the second neighborhood conjecture", 2019).

Let D be an oriented counterexample (no vertex is good) such that every nonempty oriented
digraph with fewer vertices, and every digraph obtained from D by deleting at least one arc, has
a good vertex.  Then every vertex of D has an in-neighbour, and every nonempty proper set S of
vertices satisfies |F^2(S) \ F(S)| < |F(S) \ S| (inequality (3) of the paper).

Proof.  A nonempty proper set S closed under out-neighbours would induce a smaller
counterexample (first and second out-neighbourhoods are the same in the induced digraph), so
F(S) \ S is nonempty.  A sink is good, so every vertex v has an out-neighbour, and the
complement of v shows that v has an in-neighbour.  Fix S, let I = F(S) :&: S, E = F(S) :\: S
and g(T) = |F(T) \ (I u T)| for T in E.  For T a proper subset of E, deleting the arcs from S
to E \ T leaves a good vertex v, necessarily in S, losing the out-neighbours Q = N(v) :&: (E \ T),
and the count of its second out-neighbourhood gives g(T u Q) - g(T) < |Q|.  Adding these steps
from T = set0 to T = E gives g(E) < |E|, and F^2(S) \ F(S) = F(E) \ (I u E).

Provenance: translated from the Lean formalization of OpenAI (MinimalCounterexample.lean,
SubsetAugmentation.lean, Deletion.lean, SubsetDeficit.lean),
https://github.com/openai/math/tree/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Combinatorics/SecondNeighborhood
which proves the full statement of the conjecture, following the paper "A proof of Seymour's
second-neighborhood conjecture" of OpenAI, a model-generated manuscript that is not peer
reviewed,
https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/preprints/A-proof-of-Seymours-second-neighborhood-conjecture-September-23-2026/paper.pdf
*)

From GraphTheory Require Import digraph.
From GC.GraphLib Require digraph.
From GC.digraph.OPG_seymour_second_neighborhood_outdegree Require Import defs.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Abbreviation del_arcs := GC.GraphLib.digraph.del_arcs.
Abbreviation oriented_del_arcs := GC.GraphLib.digraph.oriented_del_arcs.
Abbreviation num_edges_del_arcs := GC.GraphLib.digraph.num_edges_del_arcs.
Abbreviation card_induced := GC.GraphLib.digraph.card_induced.

(** ** Minimality *)

(** Every nonempty oriented digraph with fewer vertices has a good vertex. *)
Definition order_minimal (D : diGraph) : Prop :=
  forall D' : diGraph, oriented D' -> 0 < #|D'| -> #|D'| < #|D| -> exists v : D', good v.

(** Deleting a set of arcs containing at least one arc leaves a good vertex. *)
Definition arc_minimal (D : diGraph) : Prop :=
  forall F : {set D * D}, [exists a in F, a.1 -- a.2] -> exists v : del_arcs F, good v.

(** The second out-neighbours of [v]: the ends of the walks of length two from [v] that are
    neither [v] nor out-neighbours of [v]. *)
Lemma in_second (D : diGraph) (v x : D) :
  (x \in second_outneigh v) = [&& x != v, ~~ (v -- x) & [exists u, (v -- u) && (u -- x)]].
Proof. exact: GC.GraphLib.digraph.in_second. Qed.

(** ** Strong connectivity *)

(** A set closed under out-neighbours induces a digraph with the same first and second
    out-neighbourhoods. *)
Lemma good_induced_closed (D : diGraph) (S : {set D}) (v : induced S) :
  NS(S) \subset S -> good v = good (val v).
Proof.
move=> cS; have NvS : N(val v) \subset S.
  by apply: subset_trans cS; apply: opn_sub_opns (valP v).
rewrite /good /main.outdeg (card_induced NvS); first by move=> x; rewrite !in_opn.
congr (_ <= _); apply: card_induced => [|x].
  apply/subsetP => x; rewrite in_second => /and3P[_ _ /existsP[u /andP[vu ux]]].
  by apply: (subsetP cS); apply: (mem_opns _ ux); rewrite (subsetP NvS) ?in_opn.
rewrite !in_second (inj_eq val_inj); congr [&& _, _ & _].
apply/existsP/existsP => -[u uP]; first by exists (val u).
case/andP: uP => vu ux; have uS : u \in S by rewrite (subsetP NvS) ?in_opn.
by exists (exist _ u uS); apply/andP.
Qed.

(** Every nonempty proper set has an out-neighbour outside it (Lean:
    OrderMinimal.nonemptyBoundary). *)
Lemma minimal_boundary (D : diGraph) (S : {set D}) :
  oriented D -> [forall v : D, ~~ good v] -> order_minimal D ->
  S != set0 -> S != setT -> NS(S) :\: S != set0.
Proof.
move=> oD bad omin S0 ST; apply/negP; rewrite setD_eq0 => cS.
have [|||v gv] := omin (induced S).
- by move=> x y; apply: oD.
- by rewrite card_sig card_gt0.
- by rewrite card_sig -cardsT; apply: proper_card; rewrite properT.
- by move: (forallP bad (val v)); rewrite -good_induced_closed // gv.
Qed.

(** Lean: NonemptyBoundary.positiveIndegree. *)
Lemma minimal_positive_indeg (D : diGraph) :
  oriented D -> [forall v : D, ~~ good v] -> order_minimal D -> positive_indeg D.
Proof.
move=> oD bad omin v.
have /set0Pn[w] : N(v) != set0.
  by rewrite -card_gt0; move: (forallP bad v); rewrite /good -ltnNge; apply: leq_ltn_trans.
rewrite in_opn => vw.
have := @minimal_boundary D [set~ v] oD bad omin; case/(_ _ _)/set0Pn => [||x].
- apply/set0Pn; exists w; rewrite !inE; apply: contraTneq vw => ->.
  by apply/negP => vv; move: (oD _ _ vv); rewrite vv.
- by apply/eqP => /setP/(_ v); rewrite !inE eqxx.
by rewrite in_setD in_NS !inE negbK => /andP[/eqP-> /exists_inP[u _ uv]]; exists u.
Qed.

(** ** The deficit *)

(** Adding steps (Lean: strict_deficit_of_augmentation).  The invariant along the steps is
    g(X) + [X nonempty] <= |X|. *)
Lemma deficit_of_augmentation (T : finType) (E : {set T}) (g : {set T} -> nat) :
  g set0 = 0 -> E != set0 ->
  (forall X : {set T}, X \subset E -> X != E ->
     exists Q : {set T}, [/\ Q != set0, Q \subset E :\: X & g (X :|: Q) < g X + #|Q|]) ->
  g E < #|E|.
Proof.
move=> g0 E0 step.
suff IH n X : #|E :\: X| <= n -> X \subset E -> g X + (X != set0) <= #|X| -> g E < #|E|.
  by apply: (IH #|E| set0); rewrite ?subset_leq_card ?subsetDl ?sub0set ?g0 ?eqxx ?cards0.
elim: n X => [|n IH] X nX XE gX; have [XE'|XnE] := eqVneq X E;
  try by move: gX; rewrite XE' E0 addn1.
  move: nX; rewrite leqn0 cards_eq0 setD_eq0 => EX.
  by case/eqP: XnE; apply/eqP; rewrite eqEsubset XE.
have [Q [Q0 QEX gQ]] := step X XE XnE.
have /set0Pn[q qQ] := Q0.
have XQ : X :&: Q = set0.
  apply/setP => x; rewrite !inE; case xQ: (x \in Q); rewrite ?andbF ?andbT //.
  by have := subsetP QEX x xQ; rewrite inE => /andP[/negPf].
apply: (IH (X :|: Q)).
- rewrite -ltnS (leq_trans _ nX) // -setDDl -(cardsID Q (E :\: X)) (setIidPr QEX).
  by rewrite -[X in X < _]add0n ltn_add2r card_gt0.
- by rewrite subUset XE (subset_trans QEX) ?subsetDl.
have -> : X :|: Q != set0 by apply/set0Pn; exists q; rewrite inE qQ orbT.
rewrite cardsU XQ cards0 subn0 addn1 (leq_trans gQ) // leq_add2r.
exact: leq_trans (leq_addr _ _) gX.
Qed.

(** Counting the second out-neighbourhood after deletion: [C] is lost, at most [B] is gained. *)
Lemma card_lost_gained (T : finType) (N2 N2' C B : {set T}) :
  C \subset N2 :\: N2' -> N2' :\: N2 \subset B -> #|N2'| + #|C| <= #|N2| + #|B|.
Proof.
move=> CN BN; rewrite -(cardsID N2 N2') -(cardsID N2' N2) setIC -!addnA leq_add2l.
by rewrite addnC leq_add ?subset_leq_card.
Qed.

Section Deletion.
Variables (D : diGraph) (F : {set D * D}) (v : D).
Local Abbreviation D' := (del_arcs F).

(** The out-neighbours of [v] lost by the deletion of the arcs of [F]. *)
Definition lost : {set D} := [set x | (v -- x) && ((v, x) \in F)].

Lemma card_lost : #|N(D'; v)| + #|lost| = #|N(v)|.
Proof.
rewrite -(cardsID lost N(v)) addnC; congr (_ + _); apply: eq_card => x; rewrite /lost !inE.
  by case: (v -- x).
by rewrite [LHS]/edge_rel /=; case: (v -- x); rewrite ?andbT.
Qed.

(** A second out-neighbour gained by the deletion is a lost out-neighbour. *)
Lemma del_second (x : D) :
  x \in @second_outneigh D' v -> x \notin second_outneigh v -> x \in lost.
Proof.
rewrite (in_second (D := D')) => /and3P[xv vx /existsP[u /andP[/andP[vu _] /andP[ux _]]]].
rewrite in_second xv /= negb_and inE.
case/orP => [/negPn vx'|/existsP[]]; last by exists u; rewrite vu.
by rewrite vx' /=; move: vx; apply: contraNT => vxF; exact/andP.
Qed.

(** A vertex bad in D and good after the deletion lost an out-neighbour. *)
Lemma del_good_lost : ~~ good v -> @good D' v -> lost != set0.
Proof.
rewrite /good /main.outdeg -ltnNge => bv; apply: contraTneq => L0.
have -> : #|N(D'; v)| = #|N(v)| by rewrite -card_lost L0 cards0 addn0.
rewrite -ltnNge; apply: leq_ltn_trans bv; apply: subset_leq_card; apply/subsetP => x x2.
by apply/negPn/negP => /(del_second x2); rewrite L0 inE.
Qed.

End Deletion.

(** One step: deleting the arcs from [S] to [E \ T] (Lean: deficitPotential_step). *)
Lemma deficit_step (D : diGraph) (S T : {set D}) :
  oriented D -> [forall v : D, ~~ good v] -> arc_minimal D ->
  T \subset NS(S) :\: S -> T != NS(S) :\: S ->
  exists Q : {set D}, [/\ Q != set0, Q \subset (NS(S) :\: S) :\: T &
    #|NS(T :|: Q) :\: ((NS(S) :&: S) :|: (T :|: Q))|
      < #|NS(T) :\: ((NS(S) :&: S) :|: T)| + #|Q|].
Proof.
set E := NS(S) :\: S; set I := NS(S) :&: S => oD bad amin TE TnE.
pose F := [set a : D * D | (a.1 \in S) && (a.2 \in E :\: T)].
have /properP[_ [b bE bT]] : T \proper E by rewrite properEneq TnE.
have /exists_inP[a aS ab] : [exists a in S, a -- b] by rewrite -in_NS; case/setDP: bE.
have [v gv] : exists v : D, @good (del_arcs F) v.
  case: (amin F) => [|v gv]; last by exists v.
  by apply/exists_inP; exists (a, b); rewrite // inE /= aS in_setD bT bE.
have bv := forallP bad v; have Q0 := del_good_lost bv gv.
(* the lost out-neighbours [Q] of [v]: [v] is in [S] and [Q] is N(v) :&: (E \ T) *)
set Q := lost F v in Q0 *.
have Qv x : x \in Q -> v -- x by rewrite /Q /lost inE => /andP[].
have QF x : x \in Q -> (v \in S) && (x \in E :\: T) by rewrite /Q /lost !inE => /andP[_].
have QET : Q \subset E :\: T by apply/subsetP => x /QF /andP[].
have vS : v \in S by case/set0Pn: Q0 => q /QF /andP[].
have QY x : x \in Q -> x \notin I :|: T.
  by move=> /QF /andP[_]; rewrite !inE => /and3P[/negPf-> /negPf->]; rewrite andbF.
(* the remaining arcs from [S] go to [I :|: T] *)
have SIT u (x : D) : u \in S -> @edge_rel (del_arcs F) u x -> x \in I :|: T.
  move=> uS /andP[ux]; rewrite !inE uS (mem_opns uS ux) /=.
  by case: (x \in T); case: (x \in S).
have NYQ x : v -- x -> x \in (I :|: T) :|: Q.
  move=> vx; rewrite in_setU; case xQ: (x \in Q); rewrite ?orbT // orbF.
  apply: SIT vS _; apply/andP; split=> //.
  by apply: contraFN xQ => vxF; rewrite /Q /lost inE vx.
have S2' (x : D) : x \in @second_outneigh (del_arcs F) v -> x \in (I :|: T) :|: NS(T).
  rewrite (in_second (D := del_arcs F)) => /and3P[_ _ /existsP[u /andP[vu ux]]].
  have := SIT _ _ vS vu; rewrite in_setU => /orP[uI|uT].
    by rewrite in_setU (SIT u) //; case/setIP: uI.
  by rewrite in_setU (mem_opns uT) ?orbT //; case/andP: ux.
(* [C] is lost from the second out-neighbourhood, at most [B] is gained *)
set C := NS(Q) :\: ((I :|: T) :|: Q :|: NS(T)).
have CN : C \subset second_outneigh v :\: @second_outneigh (del_arcs F) v.
  apply/subsetP => x /setDP[]; rewrite in_NS => /exists_inP[u uQ ux] xn.
  apply/setDP; split.
    rewrite in_second; apply/and3P; split.
    - by apply: contraTneq ux => ->; apply: oD (Qv u uQ).
    - by apply: contra xn => /NYQ h; rewrite in_setU h.
    - by apply/existsP; exists u; rewrite Qv.
  by apply: contra xn => /S2'; rewrite !in_setU => /orP[->|->]; rewrite ?orbT.
set B := Q :&: NS(T).
have BN : @second_outneigh (del_arcs F) v :\: second_outneigh v \subset B.
  apply/subsetP => x /setDP[x2' x2]; have xQ := del_second x2' x2.
  by move: (S2' x x2'); rewrite /B in_setI xQ in_setU (negPf (QY x xQ)).
have h3 := card_lost F v; rewrite -/Q in h3; clearbody Q F I E.
(* g(T u Q) + |B| = g(T) + |C| *)
have h6 : #|NS(T :|: Q) :\: (I :|: (T :|: Q))| + #|B| = #|NS(T) :\: (I :|: T)| + #|C|.
  rewrite -(cardsID (NS(T)) (NS(T :|: Q) :\: _)) -(cardsID Q (NS(T) :\: _)).
  have -> : (NS(T :|: Q) :\: (I :|: (T :|: Q))) :&: NS(T) = (NS(T) :\: (I :|: T)) :\: Q.
    apply/setP => x; rewrite NSU !inE; case: (x \in NS(T)); rewrite ?andbF ?orTb ?andbT //.
    by case: (x \in I); case: (x \in T); case: (x \in Q).
  have -> : NS(T :|: Q) :\: (I :|: (T :|: Q)) :\: NS(T) = C.
    apply/setP => x; rewrite NSU !inE; case: (x \in NS(T)); rewrite ?orbT ?andbF //=.
    by case: (x \in I); case: (x \in T); case: (x \in Q).
  have -> : (NS(T) :\: (I :|: T)) :&: Q = B.
    apply/setP => x; rewrite !inE; case xQ: (x \in Q); rewrite ?andbF ?andbT //.
    by have := QY x xQ; rewrite in_setU => /negPf->.
  by rewrite addnC addnA.
exists Q; split => //; have h4 := card_lost_gained CN BN.
have hC : #|C| < #|Q| + #|B|.
  rewrite -(ltn_add2l #|@second_outneigh (del_arcs F) v|) (leq_ltn_trans h4) //.
  rewrite addnA ltn_add2r; move: bv; rewrite /good /main.outdeg -ltnNge => /leq_trans.
  by apply; rewrite -h3 leq_add2r.
by rewrite -(ltn_add2r #|B|) h6 -addnA ltn_add2l.
Qed.

Theorem minimal_subset_deficit (D : diGraph) :
  oriented D -> 0 < #|D| -> [forall v : D, ~~ good v] -> order_minimal D -> arc_minimal D ->
  positive_indeg D /\ subset_deficit D.
Proof.
move=> oD _ bad omin amin; split; first exact: minimal_positive_indeg.
move=> S S0 ST; set I := NS(S) :&: S; set E := NS(S) :\: S.
have E0 : E != set0 by apply: minimal_boundary.
have := @deficit_of_augmentation D E (fun X => #|NS(X) :\: (I :|: X)|).
rewrite opns0 set0D cards0 => /(_ erefl E0 (fun X XE XnE => deficit_step oD bad amin XE XnE)).
suff -> : NS(E) :\: (I :|: E) = NS(NS(S)) :\: NS(S) by [].
rewrite setID -{2}(setID (NS(S)) S) NSU setDUl -/I -/E.
have -> : NS(I) :\: NS(S) = set0 by apply/eqP; rewrite setD_eq0 NS_sub ?subsetIr.
by rewrite set0U.
Qed.
