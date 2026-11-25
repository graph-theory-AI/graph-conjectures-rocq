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
