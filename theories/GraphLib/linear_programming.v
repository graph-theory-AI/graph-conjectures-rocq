(** * Attainment of the optimum of a linear program

    Over an ordered field, a feasible linear program whose objective is bounded above attains its
    maximum [lp_max].

    The proof is by Fourier-Motzkin elimination (J. Fourier, 1826; T. Motzkin, 1936).  The
    projection along one variable of the set of solutions of a system of linear inequalities is
    the set of solutions of the system made of the inequalities that do not involve the variable
    and of the positive combinations eliminating the variable of each inequality where it has a
    positive coefficient with each inequality where it has a negative one [fm_sound],
    [fm_complete].  Eliminating all the variables but t from the system "t <= c x, A x <= b"
    leaves a system of inequalities [a t <= beta], whose set of solutions is a closed half-line
    when it is nonempty and bounded above.

    A maximum of finitely many attained maxima is attained [max_of_maxima]. *)

From mathcomp Require Import boot order ssralg ssrnum.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.Theory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section LinearProgramming.
Variable R : realFieldType.

(** ** Fourier-Motzkin elimination

    The variables are [x 0], [x 1], ...  A constraint [(a, beta)] on the first [N] variables
    reads [\sum_(i < N) a_i x_i <= beta]. *)

Local Abbreviation cstr := (seq R * R)%type.
Local Abbreviation co c i := (nth 0 (c : cstr).1 i).

Definition fm_lhs (N : nat) (a : seq R) (x : nat -> R) : R := \sum_(i < N) nth 0 a i * x i.

Definition fm_sat (N : nat) (s : seq cstr) (x : nat -> R) : bool :=
  all (fun c => fm_lhs N c.1 x <= c.2) s.

Lemma fm_lhsS N a x : fm_lhs N.+1 a x = fm_lhs N a x + nth 0 a N * x N.
Proof. by rewrite /fm_lhs big_ord_recr. Qed.

Lemma fm_lhs_ext N a x y : (forall i, (i < N)%N -> x i = y i) -> fm_lhs N a x = fm_lhs N a y.
Proof. by move=> e; apply: eq_bigr => i _; rewrite e. Qed.

Lemma fm_sat_ext N s x y : (forall i, (i < N)%N -> x i = y i) -> fm_sat N s x = fm_sat N s y.
Proof. by move=> e; apply: eq_all => c; rewrite (fm_lhs_ext _ e). Qed.

(** The combination of [p] and [n] that eliminates the variable [N]. *)
Definition fm_comb (N : nat) (p n : cstr) : cstr :=
  (mkseq (fun i => - co n N * co p i + co p N * co n i) N, - co n N * p.2 + co p N * n.2).

Definition fm_elim (N : nat) (s : seq cstr) :=
  [seq c <- s | co c N == 0] ++
  [seq fm_comb N p n | p <- [seq c <- s | 0 < co c N], n <- [seq c <- s | co c N < 0]].

Lemma fm_lhs_comb N p n x :
  fm_lhs N (fm_comb N p n).1 x = - co n N * fm_lhs N p.1 x + co p N * fm_lhs N n.1 x.
Proof.
rewrite /fm_lhs /= !mulr_sumr -big_split /=; apply: eq_bigr => i _.
by rewrite nth_mkseq // mulrDl !mulrA.
Qed.

Lemma fm_sound N s x : fm_sat N.+1 s x -> fm_sat N (fm_elim N s) x.
Proof.
move=> /allP H; apply/allP => c; rewrite mem_cat => /orP[].
  by rewrite mem_filter => /andP[/eqP c0 /H]; rewrite fm_lhsS c0 mul0r addr0.
case/allpairsP => -[p n] [/= + + ->]; rewrite !mem_filter => /andP[p0 /H] + /andP[n0 /H].
rewrite /= fm_lhs_comb !fm_lhsS => hp hn.
have -> : - co n N * fm_lhs N p.1 x + co p N * fm_lhs N n.1 x =
          - co n N * (fm_lhs N p.1 x + co p N * x N) + co p N * (fm_lhs N n.1 x + co n N * x N).
  by rewrite !mulrDr addrACA [co p N * (_ * _)]mulrCA -mulrDl addNr mul0r addr0.
by rewrite lerD // ler_wpM2l // ?oppr_ge0 ?ltW.
Qed.

Lemma fm_sep (a b x y u v : R) :
  0 < a -> 0 < b -> a * x + b * y <= a * u + b * v -> (y - v) / a <= (u - x) / b.
Proof.
move=> a0 b0 h; rewrite ler_pdivrMr // mulrAC ler_pdivlMr // -subr_ge0; move: h; rewrite -subr_ge0.
by rewrite opprD addrACA -!mulrBr -mulNr opprB mulrC [_ * b]mulrC.
Qed.

Lemma fm_complete N s y :
  fm_sat N (fm_elim N s) y -> exists x0, fm_sat N.+1 s (fun i => if i == N then x0 else y i).
Proof.
move=> /allP H; pose pos := [seq c <- s | 0 < co c N]; pose neg := [seq c <- s | co c N < 0].
pose U (c : cstr) := (c.2 - fm_lhs N c.1 y) / co c N.
have UU n p : n \in neg -> p \in pos -> U n <= U p.
  rewrite !mem_filter => /andP[n0 ns] /andP[p0 ps].
  rewrite {1}/U -mulrNN -invrN opprB; apply: fm_sep; rewrite ?oppr_gt0 //.
  have /H : fm_comb N p n \in fm_elim N s.
    by rewrite mem_cat; apply/orP; right; apply/allpairsP; exists (p, n); rewrite !mem_filter n0 p0.
  by rewrite /= fm_lhs_comb.
(* a value between the lower bounds [U n] and the upper bounds [U p] *)
pose x0 := \big[Order.max/(\big[Order.min/0]_(p <- pos) U p)]_(n <- neg) U n.
exists x0; apply/allP => c cs; rewrite /= fm_lhsS eqxx.
rewrite (@fm_lhs_ext _ _ _ y); first by move=> i iN; rewrite ltn_eqF.
case: (ltrgtP 0 (co c N)) => c0.
- have cp : c \in pos by rewrite mem_filter c0.
  have : x0 <= U c.
    rewrite /x0 big_seq; apply: bigmax_le => [|n nn]; [exact: ge_bigmin_seq cp _ | exact: UU].
  by rewrite /U ler_pdivlMr // mulrC -lerBrDl addrC.
- have : U c <= x0 by apply: le_bigmax_seq; rewrite // mem_filter c0.
  by rewrite /U ler_ndivrMr // mulrC -lerBrDl addrC.
- have /H : c \in fm_elim N s by rewrite mem_cat mem_filter -c0 eqxx cs.
  by rewrite -c0 mul0r addr0.
Qed.

(** Eliminating the variables [N], ..., [N + k - 1]. *)
Lemma fm_proj k N s : exists s' : seq cstr, forall y,
  fm_sat N s' y <-> exists x, (forall i, (i < N)%N -> x i = y i) /\ fm_sat (N + k) s x.
Proof.
elim: k s => [|k IH] s.
  by exists s => y; rewrite addn0; split => [|[x [/fm_sat_ext <-]]]; first exists y.
have [s' Hs'] := IH (fm_elim (N + k) s); exists s' => y; rewrite addnS; split.
  case/Hs' => x [e /fm_complete[x0 h]]; eexists; split; last exact: h.
  by move=> i iN /=; rewrite ltn_eqF ?e // ltn_addr.
by case=> x [e /fm_sound h]; apply/Hs'; exists x.
Qed.

(** ** Linear programs with nat-indexed variables *)

Lemma fm_max K (s : seq cstr) (c : seq R) :
  (exists x, fm_sat K s x) -> (exists M, forall x, fm_sat K s x -> fm_lhs K c x <= M) ->
  exists x, fm_sat K s x /\ forall x', fm_sat K s x' -> fm_lhs K c x' <= fm_lhs K c x.
Proof.
move=> [x0 hx0] [M hM].
(* the variable 0 is t, the others are those of x shifted by one *)
pose S := (1 :: map -%R c, 0) :: [seq (0 :: d.1, d.2) | d <- s].
have lhsC a0 a x : fm_lhs K.+1 (a0 :: a) x = a0 * x 0%N + fm_lhs K a (x \o succn).
  by rewrite /fm_lhs big_ord_recl.
have lhsN x : fm_lhs K (map -%R c) x = - fm_lhs K c x.
  rewrite /fm_lhs -sumrN; apply: eq_bigr => i _; case: (ltnP i (size c)) => ic.
    by rewrite (nth_map 0) // mulNr.
  by rewrite !nth_default ?size_map ?mul0r ?oppr0.
have satS x : fm_sat K.+1 S x = (x 0%N <= fm_lhs K c (x \o succn)) && fm_sat K s (x \o succn).
  rewrite /fm_sat /= lhsC mul1r lhsN subr_le0 all_map; congr (_ && _).
  by apply: eq_all => d /=; rewrite lhsC mul0r add0r.
have [s1 Hs1] := fm_proj K 1 S.
pose T t := fm_sat 1 s1 (fun _ => t).
have TE t : T t <-> exists x, fm_sat K s x /\ t <= fm_lhs K c x.
  split => [/Hs1[x [e]]|[x [hx ht]]].
    by rewrite add1n satS => /andP[h1 h2]; exists (x \o succn); rewrite -(e 0%N).
  apply/Hs1; exists (fun i => if i is j.+1 then x j else t).
  by split => [[]|] //; rewrite add1n satS ht hx.
have Tall t : T t = all (fun d : cstr => co d 0%N * t <= d.2) s1.
  by apply: eq_all => d; rewrite /fm_lhs big_ord1.
have [T0 TM] : T (fm_lhs K c x0) /\ forall t, T t -> t <= M.
  by split => [|t /TE[x [hx]] /le_trans]; [apply/TE; exists x0 | apply; apply: hM].
(* the maximum of t *)
pose u := \big[Order.min/M]_(d <- s1 | 0 < co d 0%N) (d.2 / co d 0%N).
have Tu t : T t -> t <= u.
  move=> Tt; rewrite /u big_seq_cond; apply: le_bigmin => [|d /andP[ds d0]]; first exact: TM.
  by move: Tt; rewrite Tall => /allP/(_ d ds); rewrite ler_pdivlMr // mulrC.
have [|x [hx ux]] := (TE u).1.
  rewrite Tall; apply/allP => d ds; move: (T0); rewrite Tall => /allP /(_ d ds).
  case: (ltrgtP 0 (co d 0%N)) => d0 h.
  - by rewrite mulrC -ler_pdivlMr //; apply: ge_bigmin_seq.
  - by apply: le_trans h; rewrite ler_nM2l // Tu.
  - by move: h; rewrite -d0 !mul0r.
by exists x; split => // x' hx'; apply: le_trans ux; apply/Tu/TE; exists x'.
Qed.

(** ** Linear programs with variables and constraints indexed by finite types *)

Theorem lp_max (I T : finType) (A : I -> T -> R) (b : I -> R) (c : T -> R) :
  let feasible X := (forall u, 0 <= X u) /\ (forall i, \sum_u A i u * X u <= b i) in
  (exists X, feasible X) -> (exists M, forall X, feasible X -> \sum_u c u * X u <= M) ->
  exists X, feasible X /\ forall Y, feasible Y -> \sum_u c u * Y u <= \sum_u c u * X u.
Proof.
move=> feas X0 [M hM]; pose vec (a : T -> R) := map a (enum T).
have vecE a u : nth 0 (vec a) (enum_rank u) = a u.
  by rewrite (nth_map u) ?nth_enum_rank // -cardE ltn_ord.
have lhsE a x : fm_lhs #|T| (vec a) x = \sum_u a u * x (enum_rank u).
  rewrite /fm_lhs (reindex (@enum_rank T)) /=; first exact/onW_bij/enum_rank_bij.
  by apply: eq_bigr => u _; rewrite vecE.
pose s := [seq (vec (A i), b i) | i <- enum I] ++
          [seq (vec (fun u' => - (u' == u)%:R), 0) | u <- enum T].
have satE x : fm_sat #|T| s x <-> feas (fun u => x (enum_rank u)).
  have lhs1 (u : T) : \sum_u' - (u' == u)%:R * x (enum_rank u') = - x (enum_rank u).
    by rewrite (bigD1 u) //= big1 ?addr0 ?eqxx ?mulN1r // => u' /negbTE ->; rewrite oppr0 mul0r.
  rewrite /fm_sat all_cat !all_map; split => [/andP[/allP h1 /allP h2]|[h1 h2]].
    split => [u|i]; last by have := h1 i; rewrite -enumT mem_enum /= lhsE => /(_ isT).
    by have := h2 u; rewrite -enumT mem_enum /= lhsE lhs1 oppr_le0 => /(_ isT).
  by apply/andP; split; apply/allP => i _ /=; rewrite lhsE ?lhs1 ?oppr_le0.
have satX X : feas X -> fm_sat #|T| s (nth 0 (vec X)).
  move=> [h1 h2]; apply/satE; split => [u|i] /=; rewrite ?vecE //.
  by under eq_bigr do rewrite vecE.
have [||x [/satE hx opt]] := @fm_max #|T| s (vec c).
- by case: X0 => X /satX hX; exists (nth 0 (vec X)).
- by exists M => x /satE /hM; rewrite lhsE.
exists (fun u => x (enum_rank u)); split => // Y /satX /opt; rewrite !lhsE.
by under eq_bigr do rewrite vecE.
Qed.

(** A sum over the elements of a subset, as a linear form. *)
Lemma sum_indicator_mul (T : finType) (P : pred T) (F : T -> R) :
  \sum_u (P u)%:R * F u = \sum_(u | P u) F u.
Proof. by rewrite [RHS]big_mkcond; apply: eq_bigr => u _; case: (P u); rewrite ?mul1r ?mul0r. Qed.

(** ** A maximum of finitely many attained maxima *)

Lemma max_of_maxima (K : finType) (P : pred K) (F : K -> R -> Prop) :
  (forall k, P k -> exists r, F k r /\ forall r', F k r' -> r' <= r) -> (exists k, P k) ->
  exists r, (exists2 k, P k & F k r) /\ forall k r', P k -> F k r' -> r' <= r.
Proof.
move=> hF [k0 Pk0]; have [r0 [F0 _]] := hF k0 Pk0.
suff [r [hr M]] : exists r, (exists2 k, P k & F k r) /\
    forall k r', k \in enum K -> P k -> F k r' -> r' <= r.
  by exists r; split => // k r'; apply: M; rewrite mem_enum.
elim: (enum K) => [|k s [r [hr M]]]; first by exists r0; split; first exists k0.
case: (boolP (P k)) => Pk; last first.
  exists r; split => // k' r'; rewrite inE => /predU1P[->|]; [by rewrite (negbTE Pk) | exact: M].
have [rk [Fk Mk]] := hF k Pk.
case: (leP rk r) => rkr; [exists r | exists rk]; split => //; try by exists k.
- move=> k' r'; rewrite inE => /predU1P[-> _ /Mk/le_trans|]; [exact | exact: M].
- move=> k' r'; rewrite inE => /predU1P[-> _ /Mk //|k's Pk' /(M _ _ k's Pk') h].
  exact: le_trans h (ltW rkr).
Qed.

End LinearProgramming.
