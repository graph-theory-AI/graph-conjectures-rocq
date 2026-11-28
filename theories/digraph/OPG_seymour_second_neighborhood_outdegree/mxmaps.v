(** * The four maps of the pruning lemma and the kernel conflict property

For families [R] (left) and [C] (right) of pairs of vertices of a digraph [G], and coefficients
[a b : G * G -> rat], the paper of OpenAI (Section 3) defines four maps L : Q^R -> Q^Z,
N : Q^Z -> Q^C, B : Q^R -> Q^H, A : Q^H -> Q^C with NL = AB, where Z and H are the corners of
the conflicts ([Zset], [Hset]).  The coefficient of the pair (x,y) is [coef a x y]: [a (x,y)]
on an arc x -> y, 0 otherwise (so the support condition of the paper holds by construction).

MathComp acts on row vectors, so each map is represented by the transpose of the matrix of the
paper: [L_mx a : 'M_(#|R|, #|Z|)] has entry a_{p i} in row (p,j), column (i,j), and the
identity becomes [L_mx a *m N_mx b = B_mx b *m A_mx a].  The kernel of L in the paper is the
left kernel of [L_mx a]; a vector [v] of the kernel of the transpose of N satisfies
[N_mx b *m v^T = 0].

The coefficients [b] have locally maximal ranks when, for every pair (p,i), the matrix
D^{p,i} = (b_{s j}) (s with (i,s) in C, j with (p,j) in R, entries 0 outside the arcs s -> j)
has maximum rank among the matrices with the same support.  Then a vector of the left kernel
of B and a vector of the kernel of the transpose of N have disjoint supports on each conflict
(equation (14) of the paper), by Lemma 3.2 of the paper ([kernel_support]).

Provenance: the paper "A proof of Seymour's second-neighborhood conjecture" of OpenAI, a
model-generated manuscript that is not peer reviewed,
https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/preprints/A-proof-of-Seymours-second-neighborhood-conjecture-September-23-2026/paper.pdf
and its Lean formalization (MatrixMaps.lean, MatrixMapsCommute.lean, MaxSupportKernel.lean,
KernelRestriction.lean, KernelConflict.lean),
https://github.com/openai/math/tree/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Combinatorics/SecondNeighborhood
which proves the full statement of the conjecture. *)

From GraphTheory Require Import digraph.
From GC.GraphLib Require Import linear_algebra.
From GC.digraph.OPG_seymour_second_neighborhood_outdegree Require Import defs.
From mathcomp Require Import boot order algebra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** ** Maximum support rank *)

(** If [D] has maximum rank among the matrices supported on [T], a left kernel vector [y] and a
    right kernel vector [x] satisfy [y_s x_j = 0] on [T] (Lemma 3.2 of the paper): otherwise
    adding the elementary matrix at (s,j) would increase the rank. *)
Lemma kernel_support m n (D : 'M[rat]_(m, n)) (T : 'I_m -> 'I_n -> bool) :
  (forall s j, ~~ T s j -> D s j = 0) ->
  (forall D' : 'M[rat]_(m, n), (forall s j, ~~ T s j -> D' s j = 0) -> (\rank D' <= \rank D)%N) ->
  forall (y : 'rV[rat]_m) (x : 'rV[rat]_n), y *m D = 0 -> D *m x^T = 0 ->
  forall s j, T s j -> y 0 s * x 0 j = 0.
Proof.
move=> DT Dmax y x yD Dx s j Tsj; apply/eqP/negPn/negP; rewrite mulf_eq0 negb_or.
case/andP=> ys xj; pose e : 'rV[rat]_n := delta_mx 0 j; pose D' := D + delta_mx s j.
have D'T s' j' : ~~ T s' j' -> D' s' j' = 0.
  move=> nT; rewrite !mxE DT // add0r.
  by case: (s' =P s) nT => [->|] //; case: (j' =P j) => [->|]; rewrite ?Tsj.
(* e = y D' / y_s lies in the row space of D' *)
have eD' : (e <= D')%MS.
  have <- : (y 0 s)^-1 *: (y *m D') = e.
    rewrite mulmxDr yD add0r; apply/rowP => k; rewrite !mxE (bigD1 s) //= big1.
      by move=> l /negbTE ls; rewrite mxE ls mulr0.
    by rewrite mxE eqxx addr0 mulrA mulVf // mul1r.
  exact/scalemx_sub/submxMl.
have DD' : (D <= D')%MS.
  have -> : D = D' + (-1) *: (delta_mx s 0 *m e) by rewrite mul_delta_mx scaleN1r addrK.
  by rewrite addmx_sub ?submx_refl // scalemx_sub // (submx_trans (submxMl _ _) eD').
(* but not in the row space of D, which is orthogonal to x *)
have neD : ~~ (e <= D)%MS.
  apply/negP => /submxP[w ew]; move: (congr1 (mulmx^~ x^T) ew).
  rewrite -mulmxA Dx mulmx0 => /matrixP/(_ 0 0); rewrite !mxE (bigD1 j) //= big1.
    by move=> k /negbTE kj; rewrite !mxE kj mul0r.
  by rewrite !mxE !eqxx mul1r addr0; apply/eqP.
have : (D < D')%MS by rewrite ltmxE DD' /=; apply: contra neD; apply: submx_trans.
by move/rank_ltmx; rewrite ltnNge Dmax.
Qed.

(** ** Sums over the members of a set *)

Local Lemma sum_idx (T : finType) (S : {set T}) (F : T -> rat) :
  \sum_(k : 'I_#|S|) F (idx k) = \sum_(t in S) F t.
Proof. by rewrite -big_enum_val. Qed.

(** A sum with at most one nonzero term. *)
Local Lemma sum_single (T : finType) (S : {set T}) (t0 : T) (F : T -> rat) :
  \sum_(t in S) (if t == t0 then F t else 0) = if t0 \in S then F t0 else 0.
Proof.
rewrite -big_mkcondr; case: ifP => St0.
  by rewrite (big_pred1 t0) // => t; rewrite /= andb_idl // => /eqP->.
by rewrite big_pred0 // => t; apply/andP => -[St /eqP tt0]; rewrite -tt0 St in St0.
Qed.

Local Lemma mul_if (P Q : bool) (x y : rat) :
  (if P then x else 0) * (if Q then y else 0) = if P && Q then x * y else 0.
Proof. by case: P; case: Q; rewrite ?mulr0 ?mul0r. Qed.

(** ** The four maps *)

Section Maps.
Variables (G : diGraph) (R C : {set G * G}).
Local Abbreviation Z := (Zset R C).
Local Abbreviation H := (Hset R C).
Implicit Types (a b : G * G -> rat).

(** The coefficient of the pair (x,y): [a (x,y)] on an arc, 0 otherwise. *)
Definition coef a (x y : G) : rat := if x -- y then a (x, y) else 0.

(** L maps the left member (p,j) to the points (i,j), with coefficient a_{p i}. *)
Definition L_mx a : 'M[rat]_(#|R|, #|Z|) :=
  \matrix_(r, z) (if (idx r).2 == (idx z).2 then coef a (idx r).1 (idx z).1 else 0).

(** N maps the point (i,j) to the right members (i,s), with coefficient b_{s j}. *)
Definition N_mx b : 'M[rat]_(#|Z|, #|C|) :=
  \matrix_(z, c) (if (idx c).1 == (idx z).1 then coef b (idx c).2 (idx z).2 else 0).

(** B maps the left member (p,j) to the corners (p,s), with coefficient b_{s j}. *)
Definition B_mx b : 'M[rat]_(#|R|, #|H|) :=
  \matrix_(r, h) (if (idx h).1 == (idx r).1 then coef b (idx h).2 (idx r).2 else 0).

(** A maps the corner (p,s) to the right members (i,s), with coefficient a_{p i}. *)
Definition A_mx a : 'M[rat]_(#|H|, #|C|) :=
  \matrix_(h, c) (if (idx c).2 == (idx h).2 then coef a (idx h).1 (idx c).1 else 0).

(** A nonzero product a_{p i} b_{s j} comes from a conflict between (p,j) and (i,s). *)
Local Lemma coef_conflict a b (x y : G * G) :
  coef a x.1 y.1 * coef b y.2 x.2 != 0 -> conflict x y.
Proof.
by rewrite /coef /conflict; case: (x.1 -- y.1); case: (y.2 -- x.2); rewrite ?mul0r ?mulr0 ?eqxx.
Qed.

(** Both routes from (p,j) in R to (i,s) in C give a_{p i} b_{s j} on a conflict, 0 otherwise
    (equation (11) of the paper). *)
Theorem maps_commute a b : L_mx a *m N_mx b = B_mx b *m A_mx a.
Proof.
apply/matrixP => r c; rewrite !mxE; set x := idx r; set y := idx c.
transitivity (\sum_(z in Z) if z == (y.1, x.2) then coef a x.1 z.1 * coef b y.2 z.2 else 0).
  rewrite -sum_idx; apply: eq_bigr => z _; rewrite !mxE -/x -/y mul_if.
  by case: (idx z) => i j; rewrite xpair_eqE andbC; congr (if _ && _ then _ else _); exact: eq_sym.
transitivity (\sum_(h in H) if h == (x.1, y.2) then coef a h.1 y.1 * coef b h.2 x.2 else 0).
  rewrite !sum_single /=.
  have [/coef_conflict cf|/negPn/eqP->] := boolP (coef a x.1 y.1 * coef b y.2 x.2 != 0).
    by rewrite (conflict_Zset (idxP r) (idxP c) cf) (conflict_Hset (idxP r) (idxP c) cf).
  by rewrite !if_same.
rewrite -sum_idx; apply: eq_bigr => h _; rewrite !mxE -/x -/y mul_if mulrC.
by case: (idx h) => p s; rewrite xpair_eqE; congr (if _ && _ then _ else _); exact: eq_sym.
Qed.

(** The second coordinates s of the right members (i,s), and j of the left members (p,j). *)
Definition row_fiber (i : G) : {set G} := [set s | (i, s) \in C].
Definition col_fiber (p : G) : {set G} := [set j | (p, j) \in R].

(** The matrix D^{p,i} = (b_{s j}). *)
Definition D_mx b (p i : G) : 'M[rat]_(#|row_fiber i|, #|col_fiber p|) :=
  \matrix_(s, j) coef b (idx s) (idx j).

(** For every pair (p,i), D^{p,i} has maximum rank among the matrices supported on the arcs. *)
Definition local_max_rank b : Prop :=
  forall (p i : G) (D' : 'M[rat]_(#|row_fiber i|, #|col_fiber p|)),
    (forall s j, ~~ (idx s -- idx j) -> D' s j = 0) -> (\rank D' <= \rank (D_mx b p i))%N.

(** The members of [S] of first coordinate [i]. *)
Local Lemma fiber_sum (S : {set G * G}) (i : G) (F : G * G -> rat) :
  \sum_(t in S) (if t.1 == i then F t else 0) = \sum_(s in [set s | (i, s) \in S]) F (i, s).
Proof.
have inj : {in [set s | (i, s) \in S] &, injective (pair i)} by move=> s s' _ _ [].
rewrite -big_mkcondr -(big_imset _ inj); apply: eq_bigl => -[i' s'] /=.
apply/andP/imsetP => [[tS /eqP ii]|[s0 + [-> ->]]]; first by exists s'; rewrite -?ii ?inE.
by rewrite inE => ->.
Qed.

(** A sum over the indices of [S], seen as members of [S]. *)
Local Lemma sum_rank (S : {set G * G}) t0 (t0S : t0 \in S) (F : G * G -> rat) (w : 'I_#|S| -> rat) :
  \sum_(k : 'I_#|S|) F (idx k) * w k = \sum_(t in S) F t * w (enum_rank_in t0S t).
Proof. by rewrite -sum_idx; apply: eq_bigr => k _; rewrite /idx enum_valK_in. Qed.

(** Equation (16) of the paper: if (i,j) is in the left image of R, then
    sum_s b_{s j} v_{(i,s)} = 0 for a kernel vector [v] of the transpose of N. *)
Local Lemma N_fiber b (v : 'rV[rat]_#|C|) c0 (c0C : c0 \in C) (i j : G) :
  N_mx b *m v^T = 0 -> (i, j) \in left_image R ->
  \sum_(s in row_fiber i) coef b s j * v 0 (enum_rank_in c0C (i, s)) = 0.
Proof.
move=> Nv iL; have [iZ|niZ] := boolP ((i, j) \in Z).
  move/matrixP: Nv => /(_ (enum_rank_in iZ (i, j)) 0); rewrite !mxE => Nz.
  transitivity (\sum_(k : 'I_#|C|) (if (idx k).1 == i then coef b (idx k).2 j else 0) * v 0 k).
    rewrite [RHS](@sum_rank C c0 c0C (fun t => if t.1 == i then coef b t.2 j else 0) (v 0)).
    rewrite -(fiber_sum C i (fun t => coef b t.2 j * v 0 (enum_rank_in c0C t))).
    by apply: eq_bigr => t _; case: ifP; rewrite ?mul0r.
  by rewrite -[RHS]Nz; apply: eq_bigr => k _; rewrite !mxE /idx (enum_rankK_in iZ iZ).
rewrite big1 // => s; rewrite inE /coef => sC; case: ifP => [sj|]; rewrite ?mul0r //.
by case/negP: niZ; rewrite inE iL in_right_image; apply/existsP; exists s; rewrite sC.
Qed.

(** Equation (15) of the paper: if p -> i for some (i,s) in C, then sum_j b_{s j} u_{(p,j)} = 0
    for a left kernel vector [u] of B. *)
Local Lemma B_fiber b (u : 'rV[rat]_#|R|) r0 (r0R : r0 \in R) (p s : G) :
  u *m B_mx b = 0 -> [exists i, ((i, s) \in C) && (p -- i)] ->
  \sum_(j in col_fiber p) coef b s j * u 0 (enum_rank_in r0R (p, j)) = 0.
Proof.
move=> uB /existsP[i /andP[iC pi]]; have [pH|npH] := boolP ((p, s) \in H).
  move/matrixP: uB => /(_ 0 (enum_rank_in pH (p, s))); rewrite !mxE => uz.
  transitivity (\sum_(k : 'I_#|R|) (if (idx k).1 == p then coef b s (idx k).2 else 0) * u 0 k).
    rewrite [RHS](@sum_rank R r0 r0R (fun t => if t.1 == p then coef b s t.2 else 0) (u 0)).
    rewrite -(fiber_sum R p (fun t => coef b s t.2 * u 0 (enum_rank_in r0R t))).
    by apply: eq_bigr => t _; case: ifP; rewrite ?mul0r.
  rewrite -[RHS]uz; apply: eq_bigr => k _; rewrite !mxE /idx (enum_rankK_in pH pH) /=.
  by rewrite mulrC eq_sym.
rewrite big1 // => j; rewrite inE /coef => jR; case: ifP => [sj|]; rewrite ?mul0r //.
by case/negP: npH; rewrite inE; apply/existsP; exists i; apply/existsP; exists j; apply/and4P.
Qed.

(** Kernel vectors of B and of the transpose of N have disjoint supports on each conflict
    (equation (14) of the paper).  Proof: for a conflict between (p,j) and (i,s), the
    restriction of [u] to the members (p,_) of R is a right kernel vector of D^{p,i}, and the
    restriction of [v] to the members (i,_) of C a left kernel vector (equations (15), (16)),
    so [kernel_support] applies. *)
Theorem conflict_kernel b :
  local_max_rank b ->
  forall (u : 'rV[rat]_#|R|) (v : 'rV[rat]_#|C|), u *m B_mx b = 0 -> N_mx b *m v^T = 0 ->
  forall (r : 'I_#|R|) (c : 'I_#|C|), conflict (idx r) (idx c) -> u 0 r * v 0 c = 0.
Proof.
move=> bmax u v uB Nv r c; move: (idxP r) (idxP c); rewrite /conflict.
case Er: (idx r) => [p j]; case Ec: (idx c) => [i s] rR cC /= /andP[pi sj].
have sF : s \in row_fiber i by rewrite inE.
have jF : j \in col_fiber p by rewrite inE.
(* the restrictions of v and u to the members (i,_) of C and (p,_) of R *)
pose y := \row_(k < #|row_fiber i|) v 0 (enum_rank_in cC (i, idx k)).
pose x := \row_(k < #|col_fiber p|) u 0 (enum_rank_in rR (p, idx k)).
have yD : y *m D_mx b p i = 0.
  apply/rowP => k; rewrite !mxE.
  have iL : (i, idx k) \in left_image R.
    by move: (idxP k); rewrite !inE => pk; apply/existsP; exists p; rewrite pk.
  by rewrite -[RHS](N_fiber cC Nv iL) -sum_idx; apply: eq_bigr => t _; rewrite !mxE mulrC.
have Dx : D_mx b p i *m x^T = 0.
  apply/colP => t; rewrite !mxE.
  have iC : [exists i', ((i', idx t) \in C) && (p -- i')].
    by move: (idxP t); rewrite !inE => it; apply/existsP; exists i; rewrite it.
  by rewrite -[RHS](B_fiber rR uB iC) -sum_idx; apply: eq_bigr => k _; rewrite !mxE.
have T s' j' : ~~ (idx s' -- idx j') -> D_mx b p i s' j' = 0 by rewrite mxE /coef => /negbTE->.
have Tsj : idx (enum_rank_in sF s) -- idx (enum_rank_in jF j) by rewrite /idx !enum_rankK_in.
move: (kernel_support T (bmax p i) yD Dx Tsj); rewrite !mxE /idx !enum_rankK_in //.
have -> : enum_rank_in rR (p, j) = r by apply: enum_val_inj; rewrite enum_rankK_in // -Er.
have -> : enum_rank_in cC (i, s) = c by apply: enum_val_inj; rewrite enum_rankK_in // -Ec.
by rewrite mulrC.
Qed.

End Maps.
