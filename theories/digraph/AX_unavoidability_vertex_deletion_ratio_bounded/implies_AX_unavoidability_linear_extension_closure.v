(** * Bounded ratio under vertex deletion implies linear unavoidability of k-extensions

Assume that unvd(D) <= C unvd(D - v) for every acyclic digraph D with at least two vertices and
every vertex v of D.  Let D be a k-extension of A, with D - S = A, and let C' = max(C, 1).
Deleting the vertices of S one at a time gives unvd(D) <= C'^k max(unvd(A), |V(D)|) (the second
term covers the digraphs with at most one vertex, for which unvd(D) <= |V(D)|).  Hence, if
unvd(A) <= c|V(A)| for every member A of a family, then unvd(D) <= C'^k max(c, 1) |V(D)| for their
k-extensions.

The values unvd(D - v) used along the way exist: D - v is a subdigraph of D, hence is
unavoidable, and an unavoidable digraph has a least unavoidable order.  Unavoidability is not
decided here: the least order is only shown not to be absent, which suffices to prove a boolean
inequality.

The implication is the edge e106 of relations.json in graph-conjectures.  It was formalized in
graph-theory-rocq (digraph-theory/theories/conjectures/implications_X221.v), with a proof that
decides unavoidability and shows that 2^|V(D)| vertices suffice for an acyclic digraph D. *)

From GraphTheory Require Import digraph.
From mathcomp Require Import boot.
From GC.GraphLib Require Import digraph.
From GC.digraph.AX_unavoidability_vertex_deletion_ratio_bounded Require Import
  main(AX_unavoidability_vertex_deletion_ratio_bounded).
From GC.digraph.AX_unavoidability_linear_extension_closure Require Import
  main(AX_unavoidability_linear_extension_closure).

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** An acyclic digraph with at most one vertex has no arc: it is [#|D|]-unavoidable. *)
Lemma tournament_unavoidable_small (D : diGraph) :
  acyclic D -> #|D| <= 1 -> tournament_unavoidable D #|D|.
Proof.
move=> ac D1 T _ cT; exists (fun x => enum_val (cast_ord (esym cT) (enum_rank x))).
split=> [x y /enum_val_inj/cast_ord_inj/enum_rank_inj //|u v].
rewrite (card_le1_eqP D1 v u) // => uu.
by have /forallP/(_ v)/implyP/(_ uu) := forallP ac v; rewrite connect0.
Qed.

(** ** Deleting the added vertices one at a time *)

Section Deletion.

Variable C : nat.

Hypothesis ratio : forall (D : diGraph) (v : D), acyclic D -> 1 < #|D| ->
  forall N M : nat,
    unavoidability_number D N -> unavoidability_number (induced [set~ v]) M -> N <= C * M.

(** If the deletion of [k] vertices of [D] leaves an [M]-unavoidable digraph, then
    unvd(D) <= max(C, 1)^k max(M, |V(D)|). *)
Lemma deletion_bound (k : nat) (D : diGraph) (S : {set D}) (N M : nat) :
  acyclic D -> #|S| = k -> unavoidability_number D N ->
  tournament_unavoidable (induced (~: S)) M -> N <= maxn C 1 ^ k * maxn M #|D|.
Proof.
elim: k D S N M => [|k IH] D S N M ac cS uN uM.
  move/cards0_eq: cS => S0; rewrite expn0 mul1n (leq_trans _ (leq_maxl _ _)) //.
  apply: unavoidability_number_le uN (tournament_unavoidable_sub _ uM).
  have xS x : x \in ~: S by rewrite S0 setC0 inE.
  by exists (fun x => Sub x (xS x) : induced (~: S)); split=> [x y /(congr1 val)|].
have [s sS] : {s | s \in S} by apply/sigW/set0Pn; rewrite -card_gt0 cS.
have [D1|D2] := leqP #|D| 1.
  apply: leq_trans (unavoidability_number_le uN (tournament_unavoidable_small ac D1)) _.
  by rewrite -{1}[#|D|]mul1n leq_mul ?leq_maxr // expn_gt0 leq_maxr.
pose D' := induced [set~ s].
have uD' : tournament_unavoidable D' N := tournament_unavoidable_sub (subdigraph_induced _) uN.1.
apply: (unavoidability_number_elim uD') => N' uN'.
have acD' : acyclic D'.
  by apply/acyclic_inducedP; have /acyclic_rankP[phi inc] := ac; exists phi => u v _ _ /inc.
pose S' := [set x : D' | val x \in S].
have cS' : #|S'| = k.
  move: cS; rewrite (cardsD1 s S) sS add1n => -[<-]; rewrite -(card_imset _ val_inj).
  apply: eq_card => x; rewrite !inE; apply/imsetP/andP => [[y]|[xs xS]].
    by rewrite inE => yS ->; have := valP y; rewrite !inE.
  have xs' : x \in [set~ s] by rewrite !inE.
  by exists (Sub x xs'); rewrite ?inE.
have uM' : tournament_unavoidable (induced (~: S')) M.
  apply: tournament_unavoidable_sub uM.
  have yS (y : induced (~: S')) : val (val y) \in ~: S by have := valP y; rewrite !inE.
  exists (fun y => Sub (val (val y)) (yS y) : induced (~: S)).
  by split=> // x y [] /val_inj /val_inj.
apply: leq_trans (ratio ac D2 uN uN') _; rewrite expnS -mulnA leq_mul ?leq_maxl //.
apply: leq_trans (IH _ _ _ _ acD' cS' uN' uM') _; rewrite leq_mul2l geq_max leq_maxl /=.
by rewrite leq_max (leq_card _ val_inj) !orbT.
Qed.

End Deletion.

Theorem AX_unavoidability_vertex_deletion_ratio_bounded_implies_AX_unavoidability_linear_extension_closure :
  AX_unavoidability_vertex_deletion_ratio_bounded -> AX_unavoidability_linear_extension_closure.
Proof.
move=> [C ratio] F k [c lin]; exists (maxn C 1 ^ k * maxn c 1).
move=> D N [A [FA [ac [S [cS [i]]]]]] uN.
have AD : subdigraph A D := subdigraph_trans (subdigraph_diso (diso_sym i)) (subdigraph_induced _).
apply: (unavoidability_number_elim (tournament_unavoidable_sub AD uN.1)) => M uM.
have := deletion_bound ratio ac cS uN (tournament_unavoidable_sub (subdigraph_diso i) uM.1).
move/leq_trans; apply; rewrite -[X in _ <= X]mulnA leq_mul2l maxnMl mul1n geq_max leq_maxr andbT.
have [f [f_inj _]] := AD.
by rewrite leq_max (leq_trans (lin A M FA uM)) ?leq_mul2l ?(leq_card f f_inj) ?orbT.
Qed.

Check (AX_unavoidability_vertex_deletion_ratio_bounded_implies_AX_unavoidability_linear_extension_closure :
  GC.digraph.AX_unavoidability_vertex_deletion_ratio_bounded.main.AX_unavoidability_vertex_deletion_ratio_bounded ->
  GC.digraph.AX_unavoidability_linear_extension_closure.main.AX_unavoidability_linear_extension_closure).
Print Assumptions AX_unavoidability_vertex_deletion_ratio_bounded_implies_AX_unavoidability_linear_extension_closure.
