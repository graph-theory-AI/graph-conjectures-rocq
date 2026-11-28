(** * Choice of the coefficients of the pruning lemma

Given matchings alpha (between points of Z and members of R covering them) and beta (between
points of Z and members of C covering them), there are coefficients [a] and [b] such that
- the rows of [L_mx a] indexed by the members of R matched by alpha are independent,
- the rows of the transpose of [N_mx b] indexed by the members of C matched by beta are
  independent,
- [b] has locally maximal ranks.
The matchings need not be maximum: only these lower bounds on ranks are used (rankbound.v).

Proof (Section 3 of the paper).  The coefficients [a] and [b] are chosen separately, each by
[common_nonvanishing], for pattern minors that have witnesses by [pattern_witness].  The entries
of the matrices are written [vmx v x]: the variable [x s] where the pattern [v] is [Some s], 0
where it is [None].  A matching [M] of the allowed entries gives the minor [mpat v M] (rows and
columns of the members of [M]); when each variable determines its row and its column, the 0/1
assignment of the diagonal variables makes it the identity.
- For [a], for each vertex j, the minor of L on the edges of alpha in the block of second
  coordinate j: rows the matched members (p,j), columns their partners (i,j), entries the
  distinct variables a_{p i}.  The rows of L split into blocks by second coordinate
  ([free_rows_blocks]), each independent by [minor_free_rows].
- For [b], for each vertex i, the same minor of the transpose of N on the edges of beta in the
  block of first coordinate i (variables b_{s j}), and for each pair (p,i), the minor of
  D^{p,i} on a maximum matching of its support.  For a matrix D' with the same support,
  [rank_le_cover] with the cover of [konig_bimatching] and [minor_rank] give
  rank D' <= |cover| <= |maximum matching| <= rank D^{p,i}.

Provenance: the paper "A proof of Seymour's second-neighborhood conjecture" of OpenAI, a
model-generated manuscript that is not peer reviewed,
https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/preprints/A-proof-of-Seymours-second-neighborhood-conjecture-September-23-2026/paper.pdf
and its Lean formalization (GenericRankMatching.lean, GenericRankFamily.lean,
GenericRankGlobalMinors.lean, GenericRankSelection.lean, GenericRankCoefficients.lean),
https://github.com/openai/math/tree/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Combinatorics/SecondNeighborhood
which proves the full statement of the conjecture.  The Lean development uses one global minor
for L (block triangular determinant), maximum matchings alpha and beta, and multivariate
polynomials; here the minors are per block, alpha and beta are arbitrary matchings, and [a] and
[b] are chosen independently. *)

From GraphTheory Require Import digraph.
From GC.GraphLib Require Import konig linear_algebra.
From GC.digraph.OPG_seymour_second_neighborhood_outdegree Require Import
  defs mxmaps.
From mathcomp Require Import boot order algebra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** ** A set of pairs as a set of pairs of indices

A matching between points [x] of [Sx] and members [y] of [Sy] becomes a set of entries (row
index of [y], column index of [x]) of a matrix. *)

Section FlipIdx.
Variables (X Y : finType) (Sx : {set X}) (Sy : {set Y}) (P : {set X * Y}).

Definition flip_idx : {set 'I_#|Sy| * 'I_#|Sx|} := [set e | (idx e.2, idx e.1) \in P].

Lemma flip_idx_matching (E : X -> Y -> bool) (F : 'I_#|Sy| -> 'I_#|Sx| -> bool) :
  (forall r z, E (idx z) (idx r) -> F r z) -> bimatching E P -> bimatching F flip_idx.
Proof.
move=> EF /bimatchingP[h1 h2 h3]; apply/bimatchingP; split.
- by move=> [r z]; rewrite inE => /h1; apply: EF.
- move=> [r z] [r' z']; rewrite !inE /= => eP fP rr; subst r'.
  by case: (h3 _ _ eP fP erefl) => /idx_inj ->.
- move=> [r z] [r' z']; rewrite !inE /= => eP fP zz; subst z'.
  by case: (h2 _ _ eP fP erefl) => /idx_inj ->.
Qed.

Lemma flip_idx_rows :
  {in P, forall e, e.1 \in Sx} ->
  [set e.1 | e in flip_idx] = [set r : 'I_#|Sy| | idx r \in [set e.2 | e in P]].
Proof.
move=> PS; apply/setP => r; rewrite inE; apply/imsetP/imsetP => [[[r' z]]|[[x y] eP ry]].
  by rewrite inE /= => eP ->; exists (idx z, idx r').
have [z zx] := idx_onto (PS _ eP); by exists (r, z); rewrite // inE /= zx ry.
Qed.

End FlipIdx.

(** ** Minors on matchings *)

Section MatchingMinors.
Variables (sigma : eqType) (m n : nat) (v : 'I_m -> 'I_n -> option sigma).

(** The matrix with entry [x s] where [v] is [Some s], 0 where [v] is [None]. *)
Definition vmx (x : sigma -> rat) : 'M[rat]_(m, n) := \matrix_(r, z) oapp x 0 (v r z).

Definition vrel r z : bool := v r z != None.

(** The pattern of the minor of [vmx] on a set [M] of entries: its k-th row (column) is the
    row (column) of the k-th member of [M]. *)
Definition mpat (M : {set 'I_m * 'I_n}) : 'I_#|M| -> 'I_#|M| -> option sigma :=
  fun k l => v (idx k).1 (idx l).2.
Arguments mpat M : clear implicits.

Lemma mpat_minor M x : pattern_mx (mpat M) x = \matrix_(k, l) vmx x (idx k).1 (idx l).2.
Proof. by apply/matrixP => k l; rewrite !mxE. Qed.

(** On a matching of allowed entries where each variable determines its row and column, the
    minor has a witness. *)
Lemma mpat_witness M :
  bimatching vrel M ->
  (forall e f e' f', e \in M -> f \in M -> e' \in M -> f' \in M ->
     v e.1 f.2 != None -> v e.1 f.2 = v e'.1 f'.2 -> e.1 = e'.1 /\ f.2 = f'.2) ->
  exists x, \det (pattern_mx (mpat M) x) != 0.
Proof.
move=> /bimatchingP[h1 h2 h3] hv; apply: pattern_witness => [k|k l k' l' kl ekl].
  exact: h1 (idxP k).
have [e1 e2] := hv _ _ _ _ (idxP k) (idxP l) (idxP k') (idxP l') kl ekl.
by split; apply: idx_inj; [apply: h2 e1 | apply: h3 e2]; exact: idxP.
Qed.

Lemma mpat_free M x : \det (pattern_mx (mpat M) x) != 0 -> free_rows (vmx x) [set e.1 | e in M].
Proof.
rewrite mpat_minor.
move/(@minor_free_rows _ _ _ (vmx x) (fun k => (idx k).1) (fun k => (idx k).2)).
apply: free_rows_sub; apply/subsetP => _ /imsetP[e eM ->].
by have [k <-] := idx_onto eM; apply/imsetP; exists k.
Qed.

Lemma mpat_rank M x : \det (pattern_mx (mpat M) x) != 0 -> (#|M| <= \rank (vmx x))%N.
Proof.
rewrite mpat_minor.
exact: (@minor_rank _ _ _ (vmx x) (fun k => (idx k).1) (fun k => (idx k).2)).
Qed.

(** Blocks of rows, by a key [br]. *)
Variables (K : finType) (br : 'I_m -> K).

Definition mblk (M : {set 'I_m * 'I_n}) (k : K) := [set e in M | br e.1 == k].

Lemma mblk_witness M :
  bimatching vrel M ->
  (forall r z r' z', v r z != None -> v r z = v r' z' -> br r = br r' -> r = r' /\ z = z') ->
  forall k, exists x, \det (pattern_mx (mpat (mblk M k)) x) != 0.
Proof.
move=> mM hv k; apply: mpat_witness => [|e f e' f'].
  by apply: bimatching_sub mM; apply/subsetP => e; rewrite inE => /andP[].
rewrite !inE => /andP[_ /eqP ek] _ /andP[_ /eqP e'k] _ ne ee.
by apply: hv ne ee _; rewrite ek e'k.
Qed.

Lemma mblk_free M x (bc : 'I_n -> K) :
  (forall r z, v r z != None -> br r = bc z) ->
  (forall k, \det (pattern_mx (mpat (mblk M k)) x) != 0) ->
  free_rows (vmx x) [set e.1 | e in M].
Proof.
move=> hk hdet; apply: (@free_rows_blocks _ _ (vmx x) K br bc) => [r z|k].
  by rewrite mxE; case: (v r z) (hk r z) => [s h _|]; [exact: h | rewrite eqxx].
apply: free_rows_sub (mpat_free (hdet k)); apply/subsetP => r.
rewrite inE => /andP[/imsetP[e eM ->] /eqP ek].
by apply/imsetP; exists e; rewrite // inE eM ek /=.
Qed.

End MatchingMinors.
Arguments mpat {sigma m n} v M.

(** ** The coefficients *)

Section Coefficients.
Variables (G : diGraph) (R C : {set G * G}).
Local Abbreviation Z := (Zset R C).
Implicit Types (alpha beta : {set (G * G) * (G * G)}) (a b : G * G -> rat).

(** The members of [R] matched by [alpha], as row indices of [L_mx]. *)
Definition alpha_rows alpha : {set 'I_#|R|} := [set r | idx r \in [set e.2 | e in alpha]].

(** The members of [C] matched by [beta], as row indices of the transpose of [N_mx]. *)
Definition beta_rows beta : {set 'I_#|C|} := [set c | idx c \in [set e.2 | e in beta]].

Lemma card_alpha_rows alpha :
  bimatching (alpha_rel R C) alpha -> #|alpha_rows alpha| = #|alpha|.
Proof. by case/bimatchingP => h _ h3; apply: card_idx_imset h3 _ => e /h /and3P[]. Qed.

Lemma card_beta_rows beta :
  bimatching (beta_rel R C) beta -> #|beta_rows beta| = #|beta|.
Proof. by case/bimatchingP => h _ h3; apply: card_idx_imset h3 _ => e /h /and3P[]. Qed.

(** The variables of the entries of [L_mx], the transpose of [N_mx], and [D_mx]. *)
Definition vL (r : 'I_#|R|) (z : 'I_#|Z|) : option (G * G) :=
  if lcovers (idx r) (idx z) then Some ((idx r).1, (idx z).1) else None.

Definition vN (c : 'I_#|C|) (z : 'I_#|Z|) : option (G * G) :=
  if rcovers (idx c) (idx z) then Some ((idx c).2, (idx z).2) else None.

Definition vD (p i : G) (s : 'I_#|row_fiber C i|) (j : 'I_#|col_fiber R p|) : option (G * G) :=
  if idx s -- idx j then Some (idx s, idx j) else None.
Arguments vD : clear implicits.

Lemma L_vmx a : L_mx R C a = vmx vL a.
Proof.
by apply/matrixP => r z; rewrite !mxE /vL /lcovers /coef; case: (_ == _); case: (_ -- _).
Qed.

Lemma N_vmx b : (N_mx R C b)^T = vmx vN b.
Proof.
by apply/matrixP => c z; rewrite !mxE /vN /rcovers /coef; case: (_ == _); case: (_ -- _).
Qed.

Lemma D_vmx b p i : D_mx R C b p i = vmx (vD p i) b.
Proof. by apply/matrixP => s j; rewrite !mxE /vD /coef; case: ifP. Qed.

Lemma vL_key r z : vL r z != None -> (idx r).2 = (idx z).2.
Proof. by rewrite /vL; case: ifP => // /andP[/eqP]. Qed.

Lemma vN_key c z : vN c z != None -> (idx c).1 = (idx z).1.
Proof. by rewrite /vN; case: ifP => // /andP[/eqP]. Qed.

Lemma vL_inj r z r' z' :
  vL r z != None -> vL r z = vL r' z' -> (idx r).2 = (idx r').2 -> r = r' /\ z = z'.
Proof.
move=> + e; rewrite /vL in e *; case: ifP e => [/andP[/eqP rz _]|_ _]; last by rewrite eqxx.
case: ifP => [/andP[/eqP rz' _] [e1 e2] _ e3|_ //].
by split; apply: idx_inj; apply: injective_projections => //; rewrite -rz -rz' e3.
Qed.

Lemma vN_inj c z c' z' :
  vN c z != None -> vN c z = vN c' z' -> (idx c).1 = (idx c').1 -> c = c' /\ z = z'.
Proof.
move=> + e; rewrite /vN in e *; case: ifP e => [/andP[/eqP cz _]|_ _]; last by rewrite eqxx.
case: ifP => [/andP[/eqP cz' _] [e1 e2] _ e3|_ //].
by split; apply: idx_inj; apply: injective_projections => //; rewrite -cz -cz' e3.
Qed.

(** The matchings of [alpha] and [beta] as sets of entries of [L_mx] and of the transpose of
    [N_mx], and their blocks of rows (the second, resp. first, coordinate of the member). *)
Definition alpha_idx alpha := flip_idx Z R alpha.
Definition beta_idx beta := flip_idx Z C beta.
Definition alpha_blk alpha := mblk (fun r : 'I_#|R| => (idx r).2) (alpha_idx alpha).
Definition beta_blk beta := mblk (fun c : 'I_#|C| => (idx c).1) (beta_idx beta).

Lemma alpha_idxP alpha :
  bimatching (alpha_rel R C) alpha ->
  bimatching (vrel vL) (alpha_idx alpha) /\ alpha_rows alpha = [set e.1 | e in alpha_idx alpha].
Proof.
move=> mA; split; first by apply: flip_idx_matching mA => r z /and3P[_ _ rz]; rewrite /vrel /vL rz.
by rewrite flip_idx_rows //; case/bimatchingP: mA => h _ _ e /h /and3P[].
Qed.

Lemma beta_idxP beta :
  bimatching (beta_rel R C) beta ->
  bimatching (vrel vN) (beta_idx beta) /\ beta_rows beta = [set e.1 | e in beta_idx beta].
Proof.
move=> mB; split; first by apply: flip_idx_matching mB => c z /and3P[_ _ cz]; rewrite /vrel /vN cz.
by rewrite flip_idx_rows //; case/bimatchingP: mB => h _ _ e /h /and3P[].
Qed.

(** A maximum matching of the support of D^{p,i}. *)
Definition Dmatch p i : {set 'I_#|row_fiber C i| * 'I_#|col_fiber R p|} :=
  [arg max_(M > set0 | bimatching (vrel (vD p i)) M) #|M|].

Lemma DmatchP p i :
  bimatching (vrel (vD p i)) (Dmatch p i) /\
  forall M, bimatching (vrel (vD p i)) M -> (#|M| <= #|Dmatch p i|)%N.
Proof. by rewrite /Dmatch; case: arg_maxnP => [|M mM hM]; [exact: bimatching0 | split]. Qed.

Lemma Dmatch_witness p i : exists x, \det (pattern_mx (mpat (vD p i) (Dmatch p i)) x) != 0.
Proof.
apply: (mpat_witness (proj1 (DmatchP p i))) => e f e' f' _ _ _ _.
rewrite /vD; case: ifP => _; last by rewrite eqxx.
by case: ifP => // _ _ [/idx_inj -> /idx_inj ->].
Qed.

(** The rank of D^{p,i} is at most the size of a maximum matching of its support (König), and at
    least this size when the minor on the matching is nonzero. *)
Lemma Dmatch_max_rank b p i :
  \det (pattern_mx (mpat (vD p i) (Dmatch p i)) b) != 0 ->
  forall D' : 'M[rat]_(#|row_fiber C i|, #|col_fiber R p|),
    (forall s j, ~~ (idx s -- idx j) -> D' s j = 0) -> (\rank D' <= \rank (D_mx R C b p i))%N.
Proof.
move=> hdet D' supp; rewrite D_vmx; apply: leq_trans (mpat_rank hdet).
have [M [A [B [mM cAB AB _ _]]]] := konig_bimatching (vrel (vD p i)).
apply: leq_trans (leq_trans AB (proj2 (DmatchP p i) M mM)).
apply: rank_le_cover => s j; case E: (vrel (vD p i) s j).
  by move=> _; move: cAB => /forallP/(_ s)/forallP/(_ j); rewrite E.
have nsj : ~~ (idx s -- idx j) by move: E; rewrite /vrel /vD; case: (_ -- _).
by rewrite supp // eqxx.
Qed.

(** The minors used for [b]: the blocks of [beta], and the matchings [Dmatch p i]. *)
Definition b_size beta (k : G + G * G) : nat :=
  match k with inl i => #|beta_blk beta i| | inr pi => #|Dmatch pi.1 pi.2| end.

Definition b_pat beta (k : G + G * G) :
  'I_(b_size beta k) -> 'I_(b_size beta k) -> option (G * G) :=
  match k with
  | inl i => mpat vN (beta_blk beta i)
  | inr pi => mpat (vD pi.1 pi.2) (Dmatch pi.1 pi.2)
  end.
Arguments b_pat : clear implicits.

Theorem exists_coefficients alpha beta :
  bimatching (alpha_rel R C) alpha -> bimatching (beta_rel R C) beta ->
  exists a b : G * G -> rat,
    [/\ free_rows (L_mx R C a) (alpha_rows alpha),
        free_rows (N_mx R C b)^T (beta_rows beta) & local_max_rank R C b].
Proof.
move=> /alpha_idxP[mA ->] /beta_idxP[mB ->].
have [a ha] : exists a, forall j, \det (pattern_mx (mpat vL (alpha_blk alpha j)) a) != 0.
  exact: common_nonvanishing (mblk_witness mA vL_inj).
have [b hb] : exists b, forall k, \det (pattern_mx (b_pat beta k) b) != 0.
  apply: common_nonvanishing; case=> [i|pi]; last exact: Dmatch_witness.
  exact: (mblk_witness (br := fun c : 'I_#|C| => (idx c).1) mB vN_inj i).
exists a, b; split.
- by rewrite L_vmx; apply: (mblk_free (bc := fun z : 'I_#|Z| => (idx z).2) vL_key ha).
- rewrite N_vmx; apply: (mblk_free (bc := fun z : 'I_#|Z| => (idx z).1) vN_key) => i.
  exact: hb (inl i).
- by move=> p i; exact: Dmatch_max_rank (hb (inr (p, i))).
Qed.

End Coefficients.
