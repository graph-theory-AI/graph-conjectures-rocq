(** * Blow-up by transitive tournaments

Lemma 2.3 of the paper of OpenAI (the lexicographic product D[T_m] of Brantner, Brockman, Kay
and Snively, Theorem 4.3).

Each vertex of D is replaced by a transitive tournament on m vertices (arcs from smaller to
larger labels), with all arcs from the block of v to the block of w for each arc v -> w.  If D
is oriented with positive in-degrees and the subset deficit, and m > |D|, then the blow-up
satisfies |U| + |F^2(U)| < 2 |F(U)| for every nonempty proper U.

Proof (the counting of the Lean formalization, which replaces the block-by-block bound (6) and
(7) of the paper).  Let X = F(U), Y = F^2(U) and S the set of blocks met by U.  It suffices
that |U \ X| + |Y \ X| < |X \ U|.  The vertices of U \ X lie in distinct blocks (two labels of
one block are joined by an arc), so |U \ X| <= |D|.  The blocks of F(S) \ S lie in X \ U, so
m |F(S) \ S| <= |X \ U|.  A two-step path from U that leaves X ends in a block of
F^2(S) \ F(S) (a path inside one block is shortcut by transitivity), so
|Y \ X| <= m |F^2(S) \ F(S)|.  The subset deficit and |D| < m conclude when S is proper.  When
S = V(D), positive in-degrees give X = V(G), and U is proper.

Provenance: the paper "A proof of Seymour's second-neighborhood conjecture" of OpenAI, a
model-generated manuscript that is not peer reviewed,
https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/preprints/A-proof-of-Seymours-second-neighborhood-conjecture-September-23-2026/paper.pdf
and its Lean formalization (translated from TransitiveBlowup.lean),
https://github.com/openai/math/tree/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Combinatorics/SecondNeighborhood
which proves the full statement of the conjecture. *)

From GraphTheory Require Import digraph.
From GC.GraphLib Require digraph.
From GC.digraph.OPG_seymour_second_neighborhood_outdegree Require Import defs.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Abbreviation tt_blowup := GC.GraphLib.digraph.tt_blowup.
Abbreviation tt_edgeE := GC.GraphLib.digraph.tt_edgeE.
Abbreviation tt_blowup_oriented := GC.GraphLib.digraph.tt_blowup_oriented.

Section Blowup.
Variables (D : diGraph) (m : nat).
Implicit Types (x y z : tt_blowup D m).

Lemma tt_blowup_positive_indeg : positive_indeg D -> positive_indeg (tt_blowup D m).
Proof. by move=> pD [v a]; case: (pD v) => u uv; exists (u, a); rewrite tt_edgeE uv. Qed.

End Blowup.

(** Lean [card_add_card_lt_twice_of_sdiff]. *)
Lemma growth_of_sdiff (T : finType) (U X Y : {set T}) :
  #|U :\: X| + #|Y :\: X| < #|X :\: U| -> #|U| + #|Y| < 2 * #|X|.
Proof.
move=> h; have hY : #|Y| <= #|Y :\: X| + #|X|.
  by rewrite -(cardsID X Y) addnC leq_add2l subset_leq_card ?subsetIr.
rewrite mul2n -addnn; apply: leq_ltn_trans (leq_add (leqnn #|U|) hY) _.
rewrite addnA ltn_add2r -(cardsID X U) -(cardsID U X) setIC -addnA ltn_add2l.
exact: h.
Qed.

Theorem tt_blowup_strict_growth (D : diGraph) m :
  oriented D -> positive_indeg D -> subset_deficit D -> #|D| < m ->
  strict_growth (tt_blowup D m).
Proof.
move=> oD pD dD Dm U U0 UT; set X := NS(U); set Y := NS(X); apply: growth_of_sdiff.
pose S := [set x.1 | x in U].
(* A vertex whose block is in F(S) is in X. *)
have inX (p : tt_blowup D m) : p.1 \in NS(S) -> p \in X.
  rewrite in_NS => /existsP[_ /andP[/imsetP[q qU ->] qp]].
  by apply: (mem_opns qU); rewrite tt_edgeE qp.
have [ST|ST] := eqVneq S setT.
  have XT : X = setT.
    apply/setP => p; rewrite inE; apply: inX; case: (pD p.1) => u up.
    by apply: (mem_opns _ up); rewrite ST inE.
  rewrite XT !setDT setTD !cards0 cardsCs setCK subn_gt0 -cardsT proper_card //.
  by rewrite properT.
have S0 : S != set0 by rewrite imset_eq0.
(* The vertices of U \ X lie in distinct blocks. *)
have hU : #|U :\: X| <= #|D|.
  rewrite -(card_in_imset (f := fun x : tt_blowup D m => x.1)) ?max_card //.
  move=> [u a] [v b]; rewrite !in_setD => /andP[uX uU] /andP[vX vU] /= uv; subst v.
  case: (ltngtP a b) => [ab|ba|/val_inj-> //].
    by case/negP: vX; apply: (mem_opns uU); rewrite tt_edgeE eqxx ab orbT.
  by case/negP: uX; apply: (mem_opns vU); rewrite tt_edgeE eqxx ba orbT.
(* The blocks of F(S) \ S lie in X \ U. *)
have hX : setX (NS(S) :\: S) setT \subset X :\: U.
  apply/subsetP => p; rewrite !inE andbT => /andP[pS pFS].
  by rewrite inX // andbT; apply: contra pS => pU; exact: imset_f.
(* A two-step path from U that leaves X ends in a block of F^2(S) \ F(S). *)
have hY : Y :\: X \subset setX (NS(NS(S)) :\: NS(S)) setT.
  apply/subsetP => z; rewrite !inE andbT => /andP[zX zY].
  have zS : z.1 \notin NS(S) := contra (@inX z) zX.
  rewrite zS; case/bigcupP: zY => y; rewrite in_opn => /bigcupP[x xU]; rewrite in_opn.
  have xS : x.1 \in S by exact: imset_f.
  rewrite !tt_edgeE => /orP[xy|/andP[/eqP exy lxy]] /orP[yz|/andP[/eqP eyz lyz]].
  - exact: (mem_opns (mem_opns xS xy) yz).
  - by case/negP: zS; rewrite -eyz (mem_opns xS xy).
  - by case/negP: zS; rewrite (mem_opns xS) // exy.
  - case/negP: zX; apply: (mem_opns xU).
    by rewrite tt_edgeE exy eyz eqxx (ltn_trans lxy lyz) orbT.
move: (dD S S0 ST) (subset_leq_card hX) (subset_leq_card hY).
rewrite !cardsX cardsT card_ord => def hX' hY'; apply: leq_trans hX'.
apply: leq_trans (_ : #|NS(NS(S)) :\: NS(S)|.+1 * m <= _); last by rewrite leq_mul2r def orbT.
by rewrite mulSn -addSn leq_add // (leq_ltn_trans hU Dm).
Qed.
