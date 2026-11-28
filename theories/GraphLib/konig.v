(** * König's line colouring theorem

    The edges of a bipartite graph of maximum degree D can be coloured with D colours such that the
    edges of each colour form a matching (D. König, 1916) [line_coloring].

    It follows from a property of square matrices of natural numbers whose rows and columns have sum
    D (regular bipartite multigraphs): they are sums of D permutation matrices
    [regular_decomposition], by Hall's theorem.  A bipartite graph is represented by a matrix A,
    from the vertices of one side to those of the other side, and it becomes regular with a second
    copy of the vertices: the blocks of the matrix [double] are A, its transpose, and two diagonal
    blocks that complete the row and the column sums of A. *)

From GraphTheory Require Import preliminaries digraph sgraph connectivity.
From GC.GraphLib Require Import misc chromatic.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Regular matrices of natural numbers *)

Section Support.
Variables (T : finType) (M : T -> T -> nat) (D : nat).
Hypotheses (rowM : forall x, \sum_y M x y = D) (colM : forall y, \sum_x M x y = D).

(** The bipartite digraph of the nonzero entries. *)
Definition support_rel : rel (T + T) :=
  fun u v => if (u, v) is (inl x, inr y) then 0 < M x y else false.

Definition support : diGraph := DiGraph support_rel.

Lemma regular_perm : 0 < D -> exists2 s : T -> T, injective s & forall x, 0 < M x (s x).
Proof.
move=> D0; pose A : {set support} := [set u : T + T | if u is inl _ then true else false].
have [||N [[adjN disN] AN]] := @diHall support A.
- by move=> [x|x] [y|y] //; rewrite !inE.
- move=> S SA; pose X := [set x | (inl x : T + T) \in S].
  pose Y := [set y | [exists x in X, 0 < M x y]].
  have -> : S = inl @: X.
    apply/setP => -[x|y]; first by rewrite (mem_imset _ _ (@inl_inj T T)) inE.
    by apply/idP/imsetP => [/(subsetP SA)|[]//]; rewrite inE.
  have YN : inr @: Y \subset NS(inl @: X : {set support}).
    apply/subsetP => _ /imsetP[y + ->]; rewrite inE => /exists_inP[x xX Mxy].
    by apply/bigcupP; exists (inl x); [apply: imset_f | rewrite inE].
  apply: leq_trans (subset_leq_card YN).
  rewrite (card_imset _ (@inl_inj T T)) (card_imset _ (@inr_inj T T)).
  rewrite -(leq_pmul2r D0) -!sum_nat_const -(eq_bigr _ (fun x _ => rowM x)).
  rewrite -[leqRHS](eq_bigr _ (fun y _ => colM y)).
  apply: (@leq_trans (\sum_(x in X) \sum_(y in Y) M x y)).
    apply: leq_sum => x xX; rewrite (bigID (mem Y)) /= [X in _ + X]big1 ?addn0 // => y.
    by rewrite inE negb_exists_in => /forall_inP/(_ x xX); rewrite -eqn0Ngt => /eqP.
  rewrite exchange_big; apply: leq_sum => y _; rewrite [leqRHS](bigID (mem X)).
  exact: leq_addr.
have [x|s sN] := fin_all_exists (P := fun x y => (inl x, inr y) \in N).
  have : (inl x : support) \in A by rewrite inE.
  rewrite AN => /imsetP[[u [z|y]] uN /= eu]; have := adjN _ uN; rewrite -eu //=.
  by exists y; rewrite eu.
exists s => [x x' e|x]; last exact: (adjN _ (sN x)).
have := disN _ _ (sN x) (sN x') (inr (s x)); rewrite /= e !inE !eqxx !orbT.
by move=> /(_ isT isT)[].
Qed.

End Support.

(** A regular matrix is a sum of permutation matrices. *)
Lemma regular_decomposition (T : finType) (M : T -> T -> nat) (D : nat) :
  (forall x, \sum_y M x y = D) -> (forall y, \sum_x M x y = D) ->
  exists2 s : nat -> T -> T, forall j, j < D -> injective (s j)
    & forall x y, M x y = \sum_(j < D) (s j x == y).
Proof.
elim: D M => [|D IH] M rowM colM.
  exists (fun _ => id) => // x y; rewrite big_ord0; apply/eqP; move/eqP: (rowM x).
  by rewrite sum_nat_eq0 => /forall_inP/(_ y isT).
have [s0 inj_s0 Ms0] := regular_perm rowM colM isT.
have le x y : (s0 x == y) <= M x y by case: eqP => // <-.
have [x|y|s inj_s Ms] := IH (fun x y => M x y - (s0 x == y)).
- rewrite sumnB // rowM (bigD1 (s0 x)) //= eqxx big1 ?subn1 // => y.
  by rewrite eq_sym => /negPf->.
- have [t tK sK] := injF_bij inj_s0.
  rewrite sumnB // colM (bigD1 (t y)) //= sK eqxx big1 ?subn1 // => x.
  by apply: contraNeq; rewrite eqb0 negbK => /eqP<-; rewrite tK.
exists (fun j => if j is j'.+1 then s j' else s0) => [[|j]|x y]; [by []|exact: inj_s|].
by rewrite big_ord_recl /= -Ms subnKC.
Qed.

(** ** König's theorem *)

Section LineColoring.
Variables (G : sgraph) (A : {set G}) (F : {set {set G}}) (D : nat).
Hypotheses (bipA : bipartition A) (FE : F \subset E(G)).
Hypothesis degF : forall v, #|[set e in F | v \in e]| <= D.

Definition edge_mx (x y : G) : bool := (x \in A) && ([set x; y] \in F).

Lemma edge_mx_notin x y : edge_mx x y -> y \notin A.
Proof. by case/andP=> xA /(subsetP FE); rewrite in_edges => /bipA<-. Qed.

Lemma card_edges (x : G) (P : pred G) : (forall y, P y -> [set x; y] \in F) -> #|P| <= D.
Proof.
move=> PF; apply: leq_trans (degF x); have inj : injective (fun y => [set x; y]).
  move=> y z e; have : y \in [set x; z] by rewrite -e set22.
  have : z \in [set x; y] by rewrite e set22.
  by rewrite !inE => /pred2P[->|->] // /pred2P[].
rewrite -(card_imset P inj); apply/subset_leq_card/subsetP => _ /imsetP[y /PF yF ->].
by rewrite inE yF set21.
Qed.

Lemma row_edge_mx x : \sum_y edge_mx x y <= D.
Proof. by rewrite -big_mkcond sum1_card; apply: (card_edges (x := x)) => y /andP[]. Qed.

Lemma col_edge_mx y : \sum_x edge_mx x y <= D.
Proof.
rewrite -big_mkcond sum1_card; apply: (card_edges (x := y)) => x /andP[_].
by rewrite setUC.
Qed.

(** The blocks are indexed by booleans. *)
Definition double (u v : G * bool) : nat :=
  match u.2, v.2 with
  | false, false => edge_mx u.1 v.1
  | true, true => edge_mx v.1 u.1
  | false, true => (u.1 == v.1) * (D - \sum_y edge_mx u.1 y)
  | true, false => (u.1 == v.1) * (D - \sum_x edge_mx x u.1)
  end.

Lemma sum_double (f : G * bool -> nat) : \sum_u f u = \sum_x f (x, true) + \sum_x f (x, false).
Proof.
rewrite (eq_bigr (fun u => f (u.1, u.2))) => [[]//|].
rewrite -(pair_bigA _ (fun x b => f (x, b))) -big_split.
by apply: eq_bigr => x _; rewrite big_bool.
Qed.

Lemma sum_diag (x : G) (f : G -> nat) : \sum_y (y == x) * f y = f x.
Proof. by rewrite (bigD1 x) //= eqxx mul1n big1 ?addn0 // => y /negPf->. Qed.

Lemma row_double u : \sum_v double u v = D.
Proof.
case: u => x b; rewrite sum_double /double /=.
under [X in X + _]eq_bigr do rewrite eq_sym; under [X in _ + X]eq_bigr do rewrite eq_sym.
case: b; first by rewrite sum_diag subnKC ?col_edge_mx.
by rewrite sum_diag subnK ?row_edge_mx.
Qed.

Lemma col_double v : \sum_u double u v = D.
Proof.
case: v => y [|]; rewrite sum_double /double /= sum_diag.
  by rewrite subnKC ?row_edge_mx.
by rewrite subnK ?col_edge_mx.
Qed.

Theorem line_coloring : exists col : {set G} -> nat,
  (forall e, e \in F -> col e < D) /\ forall j, matching [set e in F | col e == j].
Proof.
have [s inj_s sE] := regular_decomposition row_double col_double.
pose colored j (e : {set G}) :=
  [exists x in A, exists y, (e == [set x; y]) && (s j (x, false) == (y, false))].
pose col e := find (colored^~ e) (iota 0 D).
have colP e : e \in F -> col e < D /\ colored (col e) e.
  move=> eF; have [x [y [xA exy]]] : exists x y, x \in A /\ e = [set x; y].
    have /edgesP[x [y [-> xy]]] := subsetP FE e eF; have := bipA xy.
    by case: (boolP (y \in A)) => yA xA; [exists y, x; rewrite setUC|exists x, y].
  have has_col : has (colored^~ e) (iota 0 D).
    have := sE (x, false) (y, false); rewrite /double /= /edge_mx xA -exy eF /= => /esym/eqP.
    rewrite (bigID (fun j : 'I_D => s j (x, false) == (y, false))) /=.
    case: (pickP (fun j : 'I_D => s j (x, false) == (y, false))) => [j sj _|no].
      apply/hasP; exists (val j); rewrite ?mem_iota ?ltn_ord //.
      by apply/exists_inP; exists x => //; apply/existsP; exists y; rewrite exy eqxx.
    by rewrite !big1 // => j; rewrite no.
  have lt : col e < D by rewrite -(size_iota 0 D) -has_find.
  by split=> //; have := nth_find 0 has_col; rewrite nth_iota.
exists col; split=> [e /colP[]//|j]; split=> [e|e e']; rewrite !inE.
  by case/andP=> eF _; apply: (subsetP FE).
have colE f : (f \in F) && (col f == j) -> exists x y,
    [/\ x \in A, y \notin A, f = [set x; y], s j (x, false) = (y, false) & j < D].
  move=> /andP[fF /eqP<-]; have [lt /exists_inP[x xA /existsP[y /andP[/eqP fxy /eqP sx]]]] :=
    colP f fF.
  exists x, y; split=> //; apply: (@edge_mx_notin x).
  by rewrite /edge_mx xA -fxy.
move=> /colE e_j /colE e'_j; have [x [y [xA yA -> sx jD]]] := e_j.
have [x' [y' [x'A y'A -> sx' _]]] := e'_j; have inj := inj_s j jD => z; rewrite !inE.
move=> /pred2P[->|->] /pred2P[eq_z|eq_z].
- by move: sx'; rewrite -eq_z sx => -[->].
- by rewrite -eq_z xA in y'A.
- by rewrite eq_z x'A in yA.
have [->] : (x, false) = (x', false) by apply: inj; rewrite sx sx' eq_z.
by rewrite eq_z.
Qed.

End LineColoring.

(** The edges of a bipartite graph [G] have a proper colouring with [Delta G] colours. *)
Corollary konig (G : sgraph) : bipartite G -> exists col : {set G} -> nat,
  (forall e, e \in E(G) -> col e < Delta G) /\ proper_edge_coloring col.
Proof.
move=> [A bipA]; have [|col [lt mat]] := @line_coloring G A E(G) (Delta G) bipA (subxx _).
  move=> v; apply: leq_trans (leq_bigmax v).
  apply: leq_trans (leq_imset_card (fun y => [set v; y]) _).
  apply/subset_leq_card/subsetP => e; rewrite inE => /andP[/edgesP[x [y [-> xy]]]].
  rewrite !inE => /pred2P[->|->]; apply/imsetP; [exists y|exists x]; rewrite ?inE // 1?setUC //.
  by rewrite sg_sym.
exists col; split=> // x y z xy xz yz; apply/eqP => eq_col; have [_ dis] := mat (col [set x; z]).
have e : [set x; y] = [set x; z].
  by apply: dis (set21 x y) (set21 x z); rewrite inE in_edges ?xy ?xz ?eq_col eqxx.
have : z \in [set x; y] by rewrite e set22.
by rewrite !inE [z == y]eq_sym (negPf yz) orbF => /eqP zx; rewrite zx sg_irrefl in xz.
Qed.

(** ** König's theorem for matchings between two finite types

A bipartite graph is given by a boolean relation [E : L -> R -> bool] between two finite types;
a matching [bimatching E M] is a set of pairs [(l, r)] with [E l r], no two of which share a
first or a second coordinate, and a vertex cover [bivcover E A B] is a pair of sets meeting
every edge.  (GraphTheory defines matchings of a simple graph as sets of 2-sets, and
[dimatching] on the vertex type of a digraph; these do not allow the two sides to have
different types.)  König's theorem [konig_bimatching] gives a matching together with a vertex
cover of at most the same size made of non-isolated vertices.  It is derived from
[min_vcover_matching] and [min_max_cover] of GraphTheory, applied to the simple graph on [L + R]
whose edges are the pairs [inl l, inr r] with [E l r] and to a smallest vertex cover.

Used by the proof of Seymour's second neighbourhood conjecture
(theories/digraph/OPG_seymour_second_neighborhood_outdegree), which follows the paper of
OpenAI, a model-generated manuscript that is not peer reviewed,
https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/preprints/A-proof-of-Seymours-second-neighborhood-conjecture-September-23-2026/paper.pdf
whose Lean formalization proves this statement from Hall's theorem (MatchingCover.lean),
https://github.com/openai/math/tree/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Combinatorics/SecondNeighborhood *)

Section Bipartite.
Variables (L R : finType) (E : L -> R -> bool).
Implicit Types (M N : {set L * R}) (A : {set L}) (B : {set R}).

(** [M] is a matching of [E]. *)
Definition bimatching M : bool :=
  [&& [forall e in M, E e.1 e.2],
      [forall e in M, forall f in M, (e.1 == f.1) ==> (e == f)] &
      [forall e in M, forall f in M, (e.2 == f.2) ==> (e == f)]].

(** [(A, B)] covers every edge of [E]. *)
Definition bivcover A B : bool := [forall l, forall r, E l r ==> (l \in A) || (r \in B)].

Lemma bimatchingP M :
  reflect [/\ {in M, forall e, E e.1 e.2}, {in M &, forall e f, e.1 = f.1 -> e = f} &
              {in M &, forall e f, e.2 = f.2 -> e = f}] (bimatching M).
Proof.
have inj2P (g : L * R -> L * R -> bool) :
  reflect {in M &, forall e f, g e f -> e = f}
          [forall e in M, forall f in M, g e f ==> (e == f)].
  apply: (iffP forall_inP) => [h e f eM fM gef|h e eM].
    by apply/eqP; move/forall_inP: (h e eM) => /(_ f fM); rewrite gef.
  by apply/forall_inP => f fM; apply/implyP => /(h e f eM fM) ->.
apply: (iffP and3P) => [[/forall_inP h1 /inj2P h2 /inj2P h3]|[h1 h2 h3]].
  by split=> // e f eM fM /eqP; [apply: h2 | apply: h3].
by split; [apply/forall_inP | apply/inj2P => e f eM fM /eqP; apply: h2 |
           apply/inj2P => e f eM fM /eqP; apply: h3].
Qed.

(** The simple graph on [L + R] with an edge [inl l -- inr r] for each [E l r]. *)
Local Definition brel (x y : L + R) : bool :=
  match x, y with inl l, inr r | inr r, inl l => E l r | _, _ => false end.

Local Lemma brel_sym : symmetric brel. Proof. by case=> ? []. Qed.
Local Lemma brel_irrefl : irreflexive brel. Proof. by case. Qed.
Local Definition BG := SGraph brel_sym brel_irrefl.

(** The edge of [BG] of a pair. *)
Local Definition phi (e : L * R) : {set BG} := [set inl e.1; inr e.2].

Local Lemma phi_inj : injective phi.
Proof.
move=> [l r] [l' r'] /setP h.
have /set2P [[<-]|//] : inl l \in phi (l', r') by rewrite -h set21.
by have /set2P [//|[<-]] : inr r \in phi (l', r') by rewrite -h set22.
Qed.

Local Lemma edge_phi (x y : BG) : x -- y -> exists2 e, E e.1 e.2 & [set x; y] = phi e.
Proof.
by case: x y => [l|r] [l'|r'] //= h; [exists (l, r') | exists (l', r); rewrite // /phi setUC].
Qed.

(** König's theorem: a matching and a vertex cover of at most the same size, made of vertices
    incident to an edge.  A smallest vertex cover [V] of [BG] has the size of a matching [M'] of
    [BG] ([min_vcover_matching]), hence is contained in the vertices of [M'] ([min_max_cover]). *)
Theorem konig_bimatching :
  exists M A B, [/\ bimatching M, bivcover A B, #|A| + #|B| <= #|M|,
                    {in A, forall l, [exists r, E l r]} & {in B, forall r, [exists l, E l r]}].
Proof.
have covT : @connectivity.vcover BG setT by apply/vcoverP => x y _; left; rewrite inE.
have [covV minV] := argmin_smallest covT.
set V := [arg min_(_ < _ | _) _] in covV minV.
have bip : bipartition [set x : BG | if x is inl _ then true else false].
  by move=> [l|r] [l'|r']; rewrite !inE.
have [M' matM' cardV] := min_vcover_matching bip (conj covV minV).
have VM' := min_max_cover covV matM' (esym cardV).
case: matM' => M'E M'inj.
have M'phi e : e \in M' -> exists2 f, E f.1 f.2 & e = phi f.
  by move=> /M'E /edgesP [x [y [-> xy]]]; apply: edge_phi.
pose M := [set e | phi e \in M'].
exists M, [set l | inl l \in V], [set r | inr r \in V]; split.
- apply/bimatchingP; split.
  + by move=> e; rewrite inE => /M'phi [f Ef /phi_inj ->].
  + move=> e f; rewrite !inE => eM fM ef; apply: phi_inj.
    by apply: (M'inj _ _ eM fM (inl e.1)); rewrite !inE ?ef eqxx.
  + move=> e f; rewrite !inE => eM fM ef; apply: phi_inj.
    by apply: (M'inj _ _ eM fM (inr e.2)); rewrite !inE ?ef eqxx ?orbT.
- apply/forallP => l; apply/forallP => r; apply/implyP => lr; rewrite !inE.
  by move/vcoverP: covV => /(_ (inl l) (inr r) lr) [->|->]; rewrite ?orbT.
- rewrite -card_sum_set cardV -(card_imset _ phi_inj); apply/eq_leq/eq_card => e.
  apply/idP/imsetP => [/[dup] /M'phi [f _ ->] fM|[f]]; last by rewrite inE => ? ->.
  by exists f; rewrite ?inE.
- move=> l; rewrite inE => /(subsetP VM') /bigcupP [e /M'phi [[l' r] /= lr ->]].
  by rewrite !inE => /orP [/eqP [->]|//]; apply/existsP; exists r.
- move=> r; rewrite inE => /(subsetP VM') /bigcupP [e /M'phi [[l r'] /= lr ->]].
  by rewrite !inE => /orP [//|/eqP [->]]; apply/existsP; exists l.
Qed.

End Bipartite.

Lemma bimatching_sub (X Y : finType) (E : X -> Y -> bool) (M M' : {set X * Y}) :
  M' \subset M -> bimatching E M -> bimatching E M'.
Proof.
move=> /subsetP MM /bimatchingP[h1 h2 h3]; apply/bimatchingP.
by split=> [e eM|e f eM fM|e f eM fM]; [apply: h1 | apply: h2 | apply: h3]; apply: MM.
Qed.

Lemma bimatching0 (X Y : finType) (E : X -> Y -> bool) : bimatching E set0.
Proof. by apply/bimatchingP; split=> [e|e f|e f]; rewrite inE. Qed.
