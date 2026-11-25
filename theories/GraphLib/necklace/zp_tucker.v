(** * A Tucker lemma for Z_p

    A combinatorial form of Dold's theorem (there is no equivariant map from a connected enough
    space to a space of smaller dimension with a free action of Z_p), on a cubical complex for the
    splitting of necklaces [zp_tucker].  For p = 2, it is close to Tucker's lemma.

    The complex K is the one of F. Meunier, "Simplotopal maps and necklace splitting", Discrete
    Mathematics 323 (2014).  Let R be the star with p paths of length n from its centre, indexed by
    Z_p.  A cell of K is a product of vertices and edges of R, one of them at least being the end
    of a path.  Z_p acts by a shift of the paths.  If the cells of K with at most M+1 factors have
    labels in Z_p x {0, ..., M-1} such that the first component of the label is equivariant, then
    some cell has a facet with another first component, and a second component that is not smaller.

    The proof uses cochains on sequences of elements of Z_p (the bar complex), with coefficients in
    Z_p.  A labelling gives a map from these cochains to the cochains of K [pull], by a sum over
    the flags of faces, and the paths of R give a map back [outer].  The composition commutes with
    the coboundary and with the action.  The cochain 1 of dimension 0 is the norm of some cochain
    w_0, the coboundary of w_0 is of the form w_1(s+1) - w_1(s) for some w_1, the coboundary of w_1
    is the norm of some w_2, etc.  The values on some chains [hemi] are equal to 1 from dimension 0
    to dimension M, but in dimension M, two consecutive first components on a flag are equal, hence
    the value is 0. *)

From mathcomp Require Import boot algebra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Local Open Scope ring_scope.

(** ** Linear functionals *)

Section Linear.
Variables (R : nzRingType) (X : Type).
Implicit Types (O : (X -> R) -> R) (u v : X -> R).

(** Linear functionals on functions, without functional extensionality. *)
Definition lin O := (forall u v, u =1 v -> O u = O v) /\
  forall a u v, O (fun x => a * u x + v x) = a * O u + O v.

Lemma linB O u v : lin O -> O (fun x => u x - v x) = O u - O v.
Proof.
case=> e l; rewrite addrC -mulN1r -l; apply: e => x.
by rewrite mulN1r addrC.
Qed.

Lemma lin0 O : lin O -> O (fun=> 0) = 0.
Proof.
move=> lO; rewrite -[RHS](subrr (O (fun=> 0))) -linB //.
by case: lO => e _; apply: e => x; rewrite subrr.
Qed.

Lemma lin_sum O (I : finType) (U : I -> X -> R) :
  lin O -> O (fun x => \sum_i U i x) = \sum_i O (U i).
Proof.
move=> lO; have [e l] := lO; elim: (index_enum I) => [|i r IH].
  by rewrite big_nil -[RHS](lin0 lO); apply: e => x; rewrite big_nil.
rewrite big_cons -IH -[O (U i)]mul1r -l; apply: e => x.
by rewrite big_cons mul1r.
Qed.

End Linear.

(** ** Cochains on sequences of elements of Z_p *)

Section Cochains.
Variable p : nat.
Local Abbreviation F := ('Z_p).
Implicit Types (l s : seq F) (u v w : seq F -> F) (d : nat).

(** The coboundary: the alternating sum of the values on the sequences minus one element. *)
Fixpoint delta u s : F := if s is x :: s' then u s' - delta (fun l => u (x :: l)) s' else 0.

Lemma eq_delta u v s : (forall l, (size l).+1 = size s -> u l = v l) -> delta u s = delta v s.
Proof.
elim: s u v => //= x s IH u v uv; rewrite uv //; congr (_ - _).
by apply: IH => l sl; rewrite uv //= sl.
Qed.

Lemma lin_delta s : lin (delta^~ s).
Proof.
split=> [u v uv|]; first exact: eq_delta.
elim: s => [|x s IH] a u v /=; first by rewrite mulr0 addr0.
by rewrite IH mulrBr opprD addrACA.
Qed.

Lemma deltaK u s : delta (delta u) s = 0.
Proof. by elim: s u => //= x s IH u; rewrite (linB _ _ (lin_delta s)) IH subr0 subrr. Qed.

(** The action of Z_p. *)
Definition sh (k : F) s := [seq x + k | x <- s].

Lemma delta_sh u k s : delta u (sh k s) = delta (fun l => u (sh k l)) s.
Proof. by elim: s u => //= x s IH u; rewrite IH. Qed.

Lemma sh0 s : sh 0 s = s.
Proof. by rewrite -[RHS]map_id; apply: eq_map => x; rewrite addr0. Qed.

Lemma shD k1 k2 s : sh k1 (sh k2 s) = sh (k2 + k1) s.
Proof. by rewrite /sh -map_comp; apply: eq_map => x /=; rewrite addrA. Qed.

(** The difference in odd dimension, the norm in even dimension. *)
Definition act d u s := if odd d then u (sh 1 s) - u s else \sum_k u (sh k s).

Lemma eq_act d u v s : (forall l, size l = size s -> u l = v l) -> act d u s = act d v s.
Proof.
move=> uv; rewrite /act; case: ifP => _; first by rewrite !uv ?size_map.
by apply: eq_bigr => k _; rewrite uv ?size_map.
Qed.

Lemma lin_act d s : lin (fun u => act d u s).
Proof.
split=> [u v uv|a u v]; first exact: eq_act.
rewrite /act; case: ifP => _; first by rewrite mulrBr opprD addrACA.
by rewrite mulr_sumr -big_split.
Qed.

Lemma act_delta d u s : act d (delta u) s = delta (act d u) s.
Proof.
rewrite /act; case: (odd d); first by rewrite (linB _ _ (lin_delta s)) delta_sh.
by rewrite (lin_sum _ (lin_delta s)); apply: eq_bigr => k _; rewrite delta_sh.
Qed.

Lemma actK d u s : act d (act d.+1 u) s = 0.
Proof.
rewrite /act /=; case: (odd d) => /=.
  apply/eqP; rewrite subr_eq0; apply/eqP; rewrite [RHS](reindex_inj (addrI 1)).
  by apply: eq_bigr => k _; rewrite shD.
rewrite sumrB; apply/eqP; rewrite subr_eq0; apply/eqP.
by rewrite [RHS](reindex_inj (addIr 1)); apply: eq_bigr => k _; rewrite shD.
Qed.

(** Cochains of dimension [d] that vanish on the sequences with two equal consecutive elements. *)
Definition nml d u := forall a x b, (size a + size b).+1 = d -> u (a ++ [:: x, x & b]) = 0.

Lemma nml_cons d u x : nml d.+1 u -> nml d (fun l => u (x :: l)).
Proof. by move=> nu a y b sab; apply: (nu (x :: a)); rewrite /= -sab. Qed.

Lemma nml_delta d u : nml d u -> nml d.+1 (delta u).
Proof.
move=> nu a; elim: a d u nu => [|y a IH] d u nu x b [sab] /=; last first.
  rewrite nu // (IH (size a + size b)%N) ?subr0 //; move: nu; rewrite -sab; exact: nml_cons.
rewrite opprB addrCA subrr addr0 -[RHS](lin0 (lin_delta b)).
by apply: eq_delta => l sl; apply: (nu [::]); rewrite -sab.
Qed.

Lemma nml_sh d u k : nml d u -> nml d (fun s => u (sh k s)).
Proof. by move=> nu a x b sab; rewrite /sh map_cat /= nu ?size_map. Qed.

Lemma nml_act d u : nml d u -> nml d (act d u).
Proof.
move=> nu a x b sab; rewrite /act; case: ifP => _.
  by rewrite (nml_sh 1 nu) // nu ?subr0.
by rewrite big1 // => k _; apply: (nml_sh k nu).
Qed.

(** A primitive of [u] for [act d]. *)
Definition prim d u s : F := let h := head 0 s in
  if odd d then \sum_(i : F | (i < h)%N) u (sh (i - h) s) else if h == 0 then u s else 0.

Lemma nml_prim d u : nml d u -> nml d (prim d u).
Proof.
move=> nu a x b sab; rewrite /prim; case: ifP => _; last by rewrite nu ?if_same.
by rewrite big1 // => i _; apply: (nml_sh _ nu).
Qed.

Lemma head_sh k s : s != [::] -> head 0 (sh k s) = head 0 s + k.
Proof. by case: s. Qed.

Lemma val_add1 (h : F) :
  (h + 1 : F) = (if h.+1 == (Zp_trunc p).+2 then 0 else h.+1)%N :> nat.
Proof.
rewrite /= modnDmr addn1; case: eqP => [->|/eqP hp]; first by rewrite modnn.
by rewrite modn_small // ltn_neqAle hp ltn_ord.
Qed.

Lemma primK d u s : s != [::] -> (forall k, act d.+1 u (sh k s) = 0) -> act d (prim d u) s = u s.
Proof.
move=> s0; rewrite /act /prim /=; case: (odd d) => /= actu; last first.
  have const k : u (sh k s) = u s.
    have ks (i : nat) : u (sh i%:R s) = u s.
      elim: i => [|i IH]; first by rewrite sh0.
      by rewrite -IH; apply/eqP; rewrite -subr_eq0 -(actu i%:R) shD mulrSr.
    by rewrite -[k]natr_Zp ks.
  rewrite (bigD1 (- head 0 s)) //= head_sh // subrr eqxx big1 ?addr0 // => k kh.
  by rewrite head_sh // addr_eq0 eq_sym eqr_oppLR (negPf kh).
rewrite head_sh //; set h := head 0 s; pose U (i : F) := u (sh (i - h) s).
have -> : \sum_(i : F | (i < (h + 1)%R)%N) u (sh (i - (h + 1)) (sh 1 s)) =
    \sum_(i : F | (i < (h + 1)%R)%N) U i.
  by apply: eq_bigr => i _; rewrite shD addrC -addrA opprD addrNK.
have Uh : U h = u s by rewrite /U subrr sh0.
rewrite val_add1; case: eqP => [hp|_]; last first.
  rewrite (bigD1 h) //= Uh -addrA [X in _ + X](_ : _ = 0) ?addr0 //; apply/eqP.
  rewrite subr_eq0; apply/eqP/eq_bigl => i.
  by rewrite ltnS [RHS]ltn_neqAle andbC.
rewrite big_pred0 // sub0r; apply/eqP; rewrite eqr_oppLR -subr_eq0 opprK -Uh.
apply/eqP; rewrite -[RHS](actu (- h)) [RHS](bigD1 h) //= shD addNr sh0 -Uh [RHS]addrC.
congr (_ + _); apply: eq_big => [i|i _]; last by rewrite shD addrC.
have hi : (h < i)%N = false by apply/negbTE; rewrite -leqNgt -ltnS hp ltn_ord.
by rewrite -(inj_eq val_inj) [RHS]neq_ltn hi orbF.
Qed.

End Cochains.

(** ** The cells of K *)

Section Cells.
Variables (p n : nat).
Hypothesis n_gt0 : (0 < n)%N.
Local Abbreviation F := 'Z_p.

(** A factor of a cell is the vertex [(false, k, r)] at distance [k] from the centre on the path
    [r], or the edge [(true, k, r)] between the vertices at distances [k] and [k.+1].  The centre is
    omitted. *)
Definition entry := (bool * nat * F)%type.
Definition cell := seq entry.
Definition vtx k (r : F) : cell := if k is _.+1 then [:: (false, k, r)] else [::].
Definition edge k (r : F) : entry := (true, k, r).
Implicit Types (x : entry) (c : cell) (phi psi : cell -> F) (l : seq F).

Definition sgn x : F := if x.1.1 then -1 else 1.

(** The facets of a cell, with signs. *)
Fixpoint facets c : seq (F * cell) := if c is x :: c' then
    (if x.1.1 then [:: (1, vtx x.1.2.+1 x.2 ++ c'); (-1, vtx x.1.2 x.2 ++ c')] else [::])
    ++ [seq (sgn x * f.1, x :: f.2) | f <- facets c']
  else [::].

(** The coboundary. *)
Definition cobd phi c : F := \sum_(f <- facets c) f.1 * phi f.2.

Lemma cobd_cons phi x c : cobd phi (x :: c) =
  (if x.1.1 then phi (vtx x.1.2.+1 x.2 ++ c) - phi (vtx x.1.2 x.2 ++ c) else 0)
  + sgn x * cobd (fun c' => phi (x :: c')) c.
Proof.
rewrite /cobd /= big_cat big_map big_distrr /=; congr (_ + _); last first.
  by apply: eq_bigr => f _; rewrite mulrA.
by case: ifP => _; rewrite ?big_nil // !big_cons big_nil mul1r mulN1r addr0.
Qed.

Lemma eq_cobd phi psi c :
  (forall f, f \in facets c -> phi f.2 = psi f.2) -> cobd phi c = cobd psi c.
Proof. by move=> e; apply: eq_big_seq => f /e->. Qed.

Lemma lin_cobd c : lin (cobd^~ c).
Proof.
split=> [phi psi e|a phi psi]; first exact: eq_cobd.
by rewrite /cobd mulr_sumr -big_split; apply: eq_bigr => f _; rewrite mulrDr mulrCA.
Qed.

Lemma cobd_const a c : cobd (fun=> a) c = 0.
Proof.
elim: c => [|x c IH]; first by rewrite /cobd big_nil.
by rewrite cobd_cons IH mulr0 subrr if_same addr0.
Qed.

Lemma cobd_vtx phi k r c : cobd phi (vtx k r ++ c) = cobd (fun c' => phi (vtx k r ++ c')) c.
Proof. by case: k => [|k] //=; rewrite cobd_cons /= add0r mul1r. Qed.

Lemma cobdK phi c : cobd (cobd phi) c = 0.
Proof.
elim: c phi => [|x c IH] phi; first by rewrite /cobd big_nil.
rewrite cobd_cons; case: x => [[[] k] r]; rewrite /sgn /=; last first.
  rewrite add0r mul1r -[RHS](IH (fun c => phi ((false, k, r) :: c))).
  by apply: eq_cobd => f _; rewrite cobd_cons /= add0r mul1r.
pose A c := phi (vtx k.+1 r ++ c) - phi (vtx k r ++ c).
have -> : cobd (fun c => cobd phi ((true, k, r) :: c)) c =
    cobd (fun c => A c - cobd (fun c => phi ((true, k, r) :: c)) c) c.
  by apply: eq_cobd => f _; rewrite cobd_cons mulN1r.
rewrite (linB _ _ (lin_cobd c)) IH subr0 (linB _ _ (lin_cobd c)).
by rewrite -cobd_vtx -(cobd_vtx phi k) mulN1r subrr.
Qed.

(** Sum over the cells of the product of the paths of [l]. *)
Fixpoint cubes l phi : F :=
  if l is r :: l' then \sum_(k < n) cubes l' (fun c => phi (edge k r :: c)) else phi [::].

(** Sum over the outer boundary of this product, where one factor is the end of its path. *)
Fixpoint outer l phi : F := if l is r :: l' then
    cubes l' (fun c => phi ((false, n, r) :: c))
    - \sum_(k < n) outer l' (fun c => phi (edge k r :: c))
  else 0.

Lemma eq_cubes l phi psi :
  (forall c, size c = size l -> phi c = psi c) -> cubes l phi = cubes l psi.
Proof.
elim: l phi psi => [|r l IH] phi psi e /=; first exact: e.
by apply: eq_bigr => k _; apply: IH => c sc; rewrite e //= sc.
Qed.

Lemma lin_cubes l : lin (cubes l).
Proof.
split=> [phi psi e|]; first exact: eq_cubes.
elim: l => //= r l IH a phi psi.
by rewrite mulr_sumr -big_split; apply: eq_bigr => k _; rewrite IH.
Qed.

Lemma cubes_cobd l phi : cubes l (cobd phi) = outer l phi - delta (fun l => cubes l phi) l.
Proof.
elim: l phi => [|r l IH] phi /=; first by rewrite /cobd big_nil subr0.
pose g k := cubes l (fun c => phi (vtx k r ++ c)).
pose h (k : 'I_n) c := phi (edge k r :: c).
transitivity (\sum_(k < n) (g k.+1 - g k - cubes l (cobd (h k)))).
  apply: eq_bigr => k _; rewrite -!(linB _ _ (lin_cubes l)); apply: eq_cubes => c _.
  by rewrite cobd_cons /= mulN1r.
rewrite sumrB -(big_mkord xpredT (fun k => g k.+1 - g k)) telescope_sumr //.
rewrite (lin_sum _ (lin_delta l)) (eq_bigr _ (fun k _ => IH (h k))) sumrB.
have -> : g n = cubes l (fun c => phi ((false, n, r) :: c)) by rewrite /g; case: (n) n_gt0.
by rewrite !opprD !opprK addrACA.
Qed.

Lemma outer_cobd l phi : outer l (cobd phi) = delta (fun l => outer l phi) l.
Proof.
have outerE psi l' : outer l' psi = cubes l' (cobd psi) + delta (fun l => cubes l psi) l'.
  by rewrite cubes_cobd subrK.
rewrite outerE (eq_cubes (fun c _ => cobdK phi c)) (lin0 (lin_cubes l)) add0r.
rewrite (eq_delta (fun l' _ => cubes_cobd l' phi)) (linB _ _ (lin_delta l)).
by rewrite deltaK subr0.
Qed.

(** The cells of K: one factor is the end of a path. *)
Definition full c := has (fun x => ~~ x.1.1 && (x.1.2 == n)) c.

Lemma facets_cons x c (P : cell -> Prop) :
  (x.1.1 -> P (vtx x.1.2.+1 x.2 ++ c)) -> (x.1.1 -> P (vtx x.1.2 x.2 ++ c)) ->
  (forall f, f \in facets c -> P (x :: f.2)) -> forall f, f \in facets (x :: c) -> P f.2.
Proof.
move=> Pt Pb Pc f; rewrite mem_cat => /orP[|/mapP[g gc ->]]; last exact: Pc.
by case: ifP => // xe; rewrite !inE => /orP[] /eqP->; [apply: Pt | apply: Pb].
Qed.

Lemma size_facet c f : f \in facets c -> (size f.2 <= size c)%N.
Proof.
elim: c f => // x c IH; apply: (facets_cons (P := fun c' => (size c' <= (size c).+1)%N)) => //.
by move=> _; case: (x.1.2) => //=.
Qed.

Lemma full_facet c f : full c -> f \in facets c -> full f.2.
Proof.
elim: c f => // x c IH f fx; have fc : x.1.1 -> full c by move: fx; rewrite /full /= => /[swap]->.
apply: (facets_cons (P := full)) => [/fc|/fc|g gc].
- by rewrite /full /= => ->; rewrite orbT.
- by case: (x.1.2) => // k; rewrite /full /= => ->; rewrite orbT.
- by move: fx; rewrite /full /= => /orP[->//|fc']; rewrite [has _ _](IH g) ?orbT.
Qed.

Lemma eq_outer l phi psi :
  (forall c, full c -> (size c <= size l)%N -> phi c = psi c) -> outer l phi = outer l psi.
Proof.
elim: l phi psi => //= r l IH phi psi e; congr (_ - _).
  by apply: eq_cubes => c sc; apply: e; rewrite /= ?sc // /full /= eqxx.
apply: eq_bigr => k _; apply: IH => c fc sc; exact: e.
Qed.

Lemma lin_outer l : lin (outer l).
Proof.
split=> [phi psi e|]; first exact: eq_outer.
elim: l => [|r l IH] a phi psi /=; first by rewrite mulr0 addr0.
rewrite (lin_cubes l).2 mulrBr mulr_sumr addrACA -opprD -big_split /=.
by congr (_ - _); apply: eq_bigr => k _; rewrite IH.
Qed.

(** The action of Z_p on cells. *)
Definition shc (k : F) c : cell := [seq (x.1, x.2 + k) | x <- c].

Lemma cubes_sh k l phi : cubes (sh k l) phi = cubes l (fun c => phi (shc k c)).
Proof. by elim: l phi => //= r l IH phi; apply: eq_bigr => j _; rewrite IH. Qed.

Lemma outer_sh k l phi : outer (sh k l) phi = outer l (fun c => phi (shc k c)).
Proof.
elim: l phi => //= r l IH phi; congr (_ - _); last by apply: eq_bigr => j _; rewrite IH.
exact: cubes_sh.
Qed.

Lemma cobd_sh k c phi : cobd phi (shc k c) = cobd (fun c => phi (shc k c)) c.
Proof.
have vtx_sh j r c' : vtx j (r + k) ++ shc k c' = shc k (vtx j r ++ c') by case: j.
elim: c phi => [|x c IH] phi; first by rewrite /cobd !big_nil.
by rewrite [shc _ _]/= !cobd_cons /= -/(shc k c) !vtx_sh IH.
Qed.

(** ** The Tucker lemma *)

Section Tucker.
Variables (M : nat) (m : cell -> F) (rk : cell -> nat).
(** The cells with at most [M.+1] factors; [m] and [rk] are the two components of the label. *)
Definition inK c := full c && (size c <= M.+1)%N.
Hypothesis m_sh : forall k c, inK c -> m (shc k c) = m c + k.
Hypothesis rk_lt : forall c, inK c -> (rk c < M)%N.
Hypothesis rk_facet : forall c f, inK c -> f \in facets c -> m f.2 = m c \/ (rk f.2 < rk c)%N.

(** Sum over the flags of faces of [c], from [c] to dimension 0, of [u] on their labels. *)
Fixpoint pull d (u : seq F -> F) c : F :=
  if d is d'.+1 then cobd (pull d' (fun l => u (m c :: l))) c else u [:: m c].

Lemma eq_pull d u v c : (forall l, size l = d.+1 -> u l = v l) -> pull d u c = pull d v c.
Proof.
elim: d u v c => [|d IH] u v c e /=; first exact: e.
by apply: eq_cobd => f _; apply: IH => l sl; rewrite e //= sl.
Qed.

Lemma lin_pull d c : lin (fun u => pull d u c).
Proof.
split=> [u v uv|]; first exact: eq_pull.
elim: d c => //= d IH c a u v; rewrite -(lin_cobd c).2.
by apply: eq_cobd => f _; rewrite IH.
Qed.

Lemma pull_delta d u c : pull d.+1 (delta u) c = cobd (pull d u) c.
Proof.
elim: d u c => [|d IH] u c.
  by rewrite [LHS](linB _ _ (lin_cobd c)) (cobd_const (_ - _)) subr0.
pose w l := u (m c :: l); rewrite -[RHS]subr0 -(cobdK (pull d w) c) -(linB _ _ (lin_cobd c)).
apply: eq_cobd => f _; rewrite -(IH w); exact: (linB u _ (lin_pull d.+1 f.2)).
Qed.

Lemma inK_facet c f : inK c -> f \in facets c -> inK f.2.
Proof.
case/andP=> fc sc cf; rewrite /inK (full_facet fc cf) /=.
exact: leq_trans (size_facet cf) sc.
Qed.

Lemma pull_sh d u k c : inK c -> pull d u (shc k c) = pull d (fun l => u (sh k l)) c.
Proof.
elim: d u c => [|d IH] u c Kc /=; first by rewrite m_sh.
rewrite cobd_sh; apply: eq_cobd => f fc; rewrite IH ?(inK_facet Kc) //.
by apply: eq_pull => l _; rewrite m_sh.
Qed.

Lemma pull_eq0 d u c : inK c -> nml d u -> (rk c < d)%N -> pull d u c = 0.
Proof.
elim: d u c => //= d IH u c Kc nu; rewrite ltnS => rc.
rewrite -(cobd_const 0 c); apply: eq_cobd => f fc; have Kf := inK_facet Kc fc.
have [mf|rf] := rk_facet Kc fc; last by apply: IH (leq_trans rf rc) => //; apply: nml_cons.
case: d nu {IH rc} => [|d] nu /=; first by rewrite -mf; apply: (nu [::]).
rewrite -(cobd_const 0 f.2); apply: eq_cobd => g _; rewrite -(lin0 (lin_pull d g.2)).
by apply: eq_pull => l sl; rewrite -mf; apply: (nu [::]); rewrite sl.
Qed.

(** Sum over the hemisphere of dimension [d] (Meunier (2014), Section 3.3), by induction. *)
Fixpoint hemi d (u : seq F -> F) : F :=
  if d is d'.+1 then hemi d' (act d' (fun l => u (0 :: l))) else u [:: 0].

Lemma eq_hemi d u v : (forall l, size l = d.+1 -> u l = v l) -> hemi d u = hemi d v.
Proof.
elim: d u v => [|d IH] u v e /=; first exact: e.
by apply: IH => l sl; apply: eq_act => l' sl'; rewrite e //= sl' sl.
Qed.

Lemma lin_hemi d : lin (hemi d).
Proof.
split=> [u v uv|]; first exact: eq_hemi.
elim: d => //= d IH a u v; rewrite -IH; apply: eq_hemi => l _.
by rewrite (lin_act d l).2.
Qed.

Lemma hemi_delta d u : hemi d.+1 (delta u) = hemi d (act d u).
Proof.
elim: d u => [|d IH] u; rewrite -[RHS]subr0.
  rewrite [LHS](linB _ _ (lin_act 0 [:: 0])); congr (_ - _).
  by rewrite /act /= subr0 sumr_const card_ord Zp_mulrn; apply/val_inj; rewrite /= modnMl.
pose w l := u (0 :: l); rewrite -[X in _ - X](lin0 (lin_hemi d)).
rewrite -[X in _ - X]((lin_hemi d).1 _ _ (actK d w)) -IH -(linB _ _ (lin_hemi d.+1)).
by apply: (@eq_hemi d.+1) => l _; rewrite -act_delta -(linB _ _ (lin_act d.+1 l)).
Qed.

Definition ev d u := hemi d (fun l => outer l (pull d u)).

Lemma act_outer d u l : (size l <= M.+1)%N ->
  act d (fun l => outer l (pull d u)) l = outer l (pull d (act d u)).
Proof.
move=> sl; have e k : outer (sh k l) (pull d u) = outer l (pull d (fun l => u (sh k l))).
  rewrite outer_sh; apply: eq_outer => c fc sc; apply: pull_sh.
  by rewrite /inK fc (leq_trans sc).
have ll := lin_outer l; rewrite /act; case: (odd d).
  rewrite e -(linB _ _ ll); apply: ll.1 => c; rewrite -(linB _ _ (lin_pull d c)).
  exact: eq_pull.
rewrite (eq_bigr _ (fun k _ => e k)) -(lin_sum _ ll); apply: ll.1 => c.
by rewrite -(lin_sum _ (lin_pull d c)); apply: eq_pull.
Qed.

Lemma ev_delta d u : (d <= M)%N -> ev d.+1 (delta u) = ev d (act d u).
Proof.
move=> dM; have e l : outer l (pull d.+1 (delta u)) = delta (fun l => outer l (pull d u)) l.
  by rewrite -outer_cobd; apply: (lin_outer l).1 => c; apply: pull_delta.
rewrite /ev (eq_hemi (fun l _ => e l)) hemi_delta; apply: eq_hemi => l sl.
by apply: act_outer; rewrite sl.
Qed.

Lemma eq_ev d u v : (forall s, size s = d.+1 -> u s = v s) -> ev d u = ev d v.
Proof.
move=> uv; apply: eq_hemi => l _; apply: (lin_outer l).1 => c.
exact: eq_pull.
Qed.

Theorem zp_tucker : False.
Proof.
have chain d : (d <= M)%N -> exists w, [/\ nml d w, ev d (act d w) = 1 &
    forall s, size s = d.+2 -> delta (act d w) s = 0].
  elim: d => [|d IH] dM.
    have e s : s != [::] -> act 0 (prim 0 (fun=> 1)) s = 1.
      by move=> s0; rewrite primK // => k; rewrite /act /= subrr.
    exists (prim 0 (fun=> 1)); split=> [|| [|x [|y []]] //= _].
    - exact: nml_prim.
    - rewrite (@eq_ev 0 _ (fun=> 1)) => [[|x s] // _|]; first exact: e.
      by rewrite /ev /= big1_eq subr0.
    - by rewrite !e // !subr0 subrr.
  have [w [nw ew dw]] := IH (ltnW dM); pose u := delta w.
  have e s : size s = d.+2 -> act d.+1 (prim d.+1 u) s = u s.
    move=> ss; apply: primK => [|k]; first by case: (s) ss.
    by rewrite {1}/act /= negbK -/(act d u _) act_delta dw ?size_map.
  exists (prim d.+1 u); split; first exact/nml_prim/nml_delta.
    by rewrite (eq_ev e) /u ev_delta // ltnW.
  move=> s ss; rewrite (@eq_delta _ _ u) ?deltaK // => l sl; apply: e.
  by case: (s) ss sl => //= ? ? [->] [->].
have [w [nw ew _]] := chain M (leqnn M).
have : ev M (act M w) = 0; last by rewrite ew => /eqP; rewrite oner_eq0.
rewrite /ev -[RHS](lin0 (lin_hemi M)); apply: eq_hemi => l sl.
rewrite -[RHS](lin0 (lin_outer l)); apply: eq_outer => c fc sc.
have Kc : inK c by rewrite /inK fc -sl.
by rewrite (pull_eq0 Kc (nml_act nw)) // rk_lt.
Qed.

End Tucker.

End Cells.
