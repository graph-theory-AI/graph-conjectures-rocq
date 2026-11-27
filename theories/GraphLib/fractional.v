(** * Fractional parameters

    Fractional and circular colourings, fractional dichromatic number, maximum average degree of
    digraphs, and fractional Hadwiger number.  Their existence relies on [lp_max] of
    [linear_programming]. *)

(* [digraph] comes last: [induced] and [induced_rel] are those of digraphs, not of sgraphs *)
From GraphTheory Require Import preliminaries sgraph dom coloring minor digraph.
From mathcomp Require Import boot order ssralg ssrnum ssrint rat.
From GC.GraphLib Require Import misc chromatic minor linear_programming.
From GC.GraphLib Require Import digraph(acyclic).

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.Theory GRing.Theory Num.Theory.

(** ** Fractional colourings *)

(** The fractional chromatic number of [G] is at most [p / q] ([0 < q] is meant): [G] has a
    [b]-fold colouring with [a] colours (each vertex receives [b] colours, and adjacent vertices
    receive disjoint sets) such that [a / b <= p / q]. *)
Definition fractional_chromatic_le (G : sgraph) (p q : nat) : Prop :=
  exists a b : nat, [/\ 0 < b, weighted_colorable (fun _ : G => b) a & a * q <= p * b].

(** The fractional chromatic number of [G] is at least the integer [k]. *)
Definition fractional_chromatic_ge (G : sgraph) (k : nat) : Prop :=
  forall a b : nat, 0 < b -> weighted_colorable (fun _ : G => b) a -> k * b <= a.

(** The fractional chromatic number of [G] is [r]. *)
Definition fractional_chromatic_number (G : sgraph) (r : rat) : Prop :=
  (exists a b : nat, (0 < b)%N /\
     weighted_colorable (fun _ : G => b) a /\ r = (a%:Q / b%:Q)%R) /\
  (forall a b : nat, (0 < b)%N ->
     weighted_colorable (fun _ : G => b) a -> (r <= a%:Q / b%:Q)%R).

(** The Hall ratio of [G] is at most [p / q]: so is the ratio of the number of vertices to the
    independence number for all its subgraphs. *)
Definition hall_ratio_le (G : sgraph) (p q : nat) : Prop :=
  forall H : sgraph, subgraph H G -> q * #|H| <= p * α([set: H]).

(** ** Circular colourings

    They are defined for a relation [adj] on a type [V], possibly infinite. *)

(** [c] is a circular [(p,q)]-colouring: its values are less than [p] and, for adjacent
    vertices, they differ by at least [q] and at most [p - q]. *)
Definition circular_coloring (V : Type) (adj : V -> V -> bool) (p q : nat) (c : V -> nat) : Prop :=
  (forall v, (c v < p)%N) /\
  (forall u v, adj u v ->
     (q <= absz (Posz (c u) - Posz (c v))%R)%N /\
     (absz (Posz (c u) - Posz (c v))%R <= p - q)%N).

(** The circular chromatic number is [r]: the least [p / q] such that there is a circular
    [(p,q)]-colouring (there is none if no two vertices are adjacent). *)
Definition circular_chromatic_number (V : Type) (adj : V -> V -> bool) (r : rat) : Prop :=
  (exists p q : nat, (0 < q)%N /\ (exists c, circular_coloring adj p q c) /\ r = (p%:Q / q%:Q)%R) /\
  (forall p q : nat, (0 < q)%N -> (exists c, circular_coloring adj p q c) -> (r <= p%:Q / q%:Q)%R).

(** [G] is circularly [t]-choosable: for all [p] and [q], it has a circular [(p,q)]-colouring
    from all lists of size at least [t * q]. *)
Definition circularly_choosable (G : sgraph) (t : rat) : Prop :=
  forall p q : nat, (0 < q)%N ->
    forall L : G -> {set 'I_p},
      (forall v, (t * q%:Q <= (#|L v|)%:Q)%R) ->
      exists c : G -> 'I_p,
        circular_coloring (fun x y : G => x -- y) p q (fun v => (c v : nat)) /\
        (forall v, c v \in L v).

(** The circular choosability of [G] is [b]: the greatest lower bound of the [t >= 1] such that
    [G] is circularly [t]-choosable. *)
Definition circular_choosability (G : sgraph) (b : rat) : Prop :=
  [/\ (1 <= b)%R,
      (forall t : rat, (b < t)%R -> circularly_choosable G t)
    & (forall t : rat, (1 <= t)%R -> circularly_choosable G t -> (b <= t)%R)].

(** ** Digraphs *)

(** Maximum average degree: the maximum of 2|A(S)|/|S| over nonempty [S] (0 if [D] is empty). *)
Definition digraph_mad (D : diGraph) : rat :=
  (\big[Num.max/0]_(S in [set S : {set D} | S != set0])
     ((2 * num_edges (induced S))%:Q / (#|S|)%:Q))%R.

(** The fractional dichromatic number of [D] is at most [p]: nonnegative weights on the
    sets inducing an acyclic digraph, of total at most [p], cover each vertex with weight
    at least 1.  Weights are taken in an ordered field [R]. *)
Definition fractional_dicolorable (R : realFieldType) (D : diGraph) (p : R) : Prop :=
  (exists x : {set D} -> R,
    [/\ forall A : {set D}, 0 <= x A,
        forall v : D, 1 <= \sum_(A : {set D} | acyclic (induced A) && (v \in A)) x A
      & \sum_(A : {set D} | acyclic (induced A)) x A <= p])%R.

(** ** Existence and bounds of the fractional chromatic number *)

Section FractionalChromatic.
Variable G : sgraph.

Local Open Scope ring_scope.

(** [χ_f(G) <= χ(G)]. *)
Lemma fractional_chromatic_le_chi r : fractional_chromatic_number G r -> r <= χ([set: G])%:Q.
Proof. by case=> _ /(_ _ 1 isT (chi_weighted_colorable G)); rewrite divr1. Qed.

(** [n <= χ_f(G) α(G)]. *)
Lemma card_le_fractional_chromatic_alpha r :
  fractional_chromatic_number G r -> #|G|%:Q <= r * α(G)%:Q.
Proof.
case=> [[a [b [b0 [/weighted_colorable_alpha h ->]]]] _].
by move: h; rewrite -(ler_nat rat) !natrM mulrAC ler_pdivlMr ?ltr0n.
Qed.

Let sum_fibres (I J : finType) (p : I -> J) (P : pred J) (w : I -> rat) :
  \sum_(j | P j) \sum_(i | p i == j) w i = \sum_(i | P (p i)) w i.
Proof.
rewrite [RHS](partition_big p P) //; apply: eq_bigr => j Pj.
by apply: eq_bigl => i; case: eqP => [->|]; rewrite ?Pj ?andbF.
Qed.

(** Every graph has a fractional chromatic number.  The linear program "minimise the sum of
    nonnegative weights on the stable sets, such that the stable sets containing any given vertex
    have total weight at least 1" attains its minimum ([lp_max]).  A [b]-fold colouring with [a]
    colours gives the weights [1 / b] to its colour classes, of total [a / b].  Conversely, if
    [D] is a common denominator of the optimal weights [Y], taking each stable set [I] as colour
    class [D Y_I] times gives at least [D] colours to each vertex, among which [D] are kept. *)
Lemma fractional_chromatic_number_exists : exists r, fractional_chromatic_number G r.
Proof.
have [||Y [[Y0 Yc] opt]] := @lp_max rat G {set G} (fun v I => - (stable I && (v \in I))%:R)
  (fun _ => -1) (fun I => - (stable I)%:R).
- exists (fun _ => 1); split => // v; under eq_bigr do rewrite mulNr mulr1.
  rewrite sumrN lerN2 (bigD1 [set v]) ?stable1 ?set11 //= lerDl.
  by apply: sumr_ge0 => I _; rewrite ler0n.
- exists 0 => X [X0 _]; rewrite -oppr_ge0 -sumrN.
  by apply: sumr_ge0 => I _; rewrite mulNr opprK mulr_ge0.
have val (X : {set G} -> rat) : \sum_I - (stable I)%:R * X I = - \sum_(I | stable I) X I.
  under eq_bigr do rewrite mulNr; by rewrite sumrN sum_indicator_mul.
have cov (X : {set G} -> rat) v : \sum_I - (stable I && (v \in I))%:R * X I =
    - \sum_(I | stable I && (v \in I)) X I.
  by under eq_bigr do rewrite mulNr; rewrite sumrN sum_indicator_mul.
exists (\sum_(I | stable I) Y I); split; last first.
  (* a b-fold colouring with a colours gives a feasible point of value a / b *)
  move=> a b b0 [f [cf df]]; pose cl (c : 'I_a) := [set v | c \in f v].
  have stab c : stable (cl c).
    apply/stableP => x y; rewrite !inE => cx cy; apply/negP => xy.
    by rewrite (disjointFr (df x y xy) cx) in cy.
  pose Y' I := \sum_(c | cl c == I) (b%:Q)^-1.
  have /opt : (forall I, 0 <= Y' I) /\
      forall v, \sum_I - (stable I && (v \in I))%:R * Y' I <= -1.
    split => [I|v]; first by apply: sumr_ge0 => c _; rewrite invr_ge0.
    rewrite cov lerN2 sum_fibres (eq_bigl (mem (f v))) => [c|]; first by rewrite stab inE.
    by rewrite sumr_const cf -mulr_natr mulVf // pnatr_eq0 -lt0n.
  rewrite !val lerN2 /Y' sum_fibres => /le_trans; apply.
  rewrite (eq_bigl predT) => [c|]; first exact: stab.
  by rewrite sumr_const card_ord -mulr_natr mulrC.
(* conversely, a common denominator of the weights gives a colouring *)
pose D := \prod_(J : {set G}) `|denq (Y J)|%N.
pose k (I : {set G}) := (`|numq (Y I)| * \prod_(J | J != I) `|denq (Y J)|)%N.
have D0 : (0 < D)%N by rewrite prodn_gt0 // => J; rewrite absz_gt0 denq_neq0.
have kE I : (k I)%:R = Y I * D%:R.
  rewrite /D (bigD1 I) //= /k !natrM mulrA; congr (_ * _).
  by rewrite !natr_absz ger0_norm ?numq_ge0 // normr_denq numqE.
pose s := flatten [seq nseq (k J) J | J <- enum {set G} & stable J].
pose a := size s; pose col (c : 'I_a) := nth set0 s c.
have stab c : stable (col c).
  have /flattenP[t /mapP[J]] : col c \in s by apply: mem_nth.
  by rewrite mem_filter => /andP[sJ _] -> /[!mem_nseq] /andP[_ /eqP ->].
have countE (Q : pred {set G}) : #|[set c : 'I_a | Q (col c)]| = (\sum_(J | stable J && Q J) k J)%N.
  rewrite -sum1_card (eq_bigl (fun c : 'I_a => Q (nth set0 s c))) => [c|]; first by rewrite inE.
  have -> : (\sum_(c < a | Q (nth set0 s c)) 1 = \sum_(x <- s | Q x) 1)%N.
    by rewrite (big_nth set0) big_mkord.
  rewrite big_flatten big_map.
  rewrite big_filter big_enum_cond /= big_mkcondr; apply: eq_bigr => J _.
  by rewrite sum1_count count_nseq; case: (Q J); rewrite ?mul1n ?mul0n.
pose C (v : G) := [set c : 'I_a | v \in col c].
pose f (v : G) := [set c in take D (enum (C v))].
have hC v : (D <= #|C v|)%N.
  have -> : #|C v| = (\sum_(J | stable J && (v \in J)) k J)%N := countE (fun J => v \in J).
  rewrite -(ler_nat rat) natr_sum; under eq_bigr do rewrite kE.
  rewrite -mulr_suml -[X in X <= _]mul1r ler_pM2r ?ltr0n //.
  by have := Yc v; rewrite cov lerN2.
exists a, D; split => //; split; last first.
  rewrite -!pmulrn; have -> : a%:R = (\sum_(J | stable J) k J)%N%:R :> rat.
    congr (_%:R); rewrite (eq_bigl (fun J => stable J && predT J)) => [J|]; first by rewrite andbT.
    by rewrite -countE -[LHS](card_ord a) -cardsT; apply: eq_card => c; rewrite !inE.
  by rewrite natr_sum (eq_bigr _ (fun J _ => kE J)) -mulr_suml mulfK // pnatr_eq0 -lt0n.
exists f; split => [v|x y xy].
  rewrite cardsE; move/card_uniqP: (take_uniq D (enum_uniq (mem (C v)))) => ->.
  by rewrite size_takel // -cardE hC.
apply/disjointP => c cx cy.
have sub v : f v \subset C v by apply/subsetP => c'; rewrite inE => /mem_take; rewrite mem_enum.
move: (subsetP (sub x) c cx) (subsetP (sub y) c cy); rewrite !inE => hx hy.
by move/stableP: (stab c) => /(_ x y hx hy); rewrite xy.
Qed.

End FractionalChromatic.

(** ** Fractional Hadwiger number *)

Section FractionalHadwiger.
Import Order.Theory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Variable G : sgraph.

(** The fractional Hadwiger number is at most the number of vertices. *)
Lemma fractional_clique_minor_le_card n (B : 'I_n -> {set G}) w r :
  fractional_clique_minor B w r -> r <= #|G|%:R.
Proof.
case=> w0 Bc _ cov ->; apply: (@le_trans _ _ (\sum_i w i * #|B i|%:R)).
  apply: ler_sum => i _; rewrite ler_peMr // ler1n lt0n cards_eq0; exact: (Bc i).1.
rewrite (eq_bigr (fun i => \sum_(v in B i) w i)); first by move=> i _; rewrite sumr_const mulr_natr.
by rewrite (exchange_big_dep predT) //= -sum1_card natr_sum; apply: ler_sum => v _; exact: cov.
Qed.

(** If [G] has a [K_n] minor, its fractional Hadwiger number is at least [n]: take the branch
    sets with weight 1. *)
Lemma minor_le_fractional_hadwiger (n : nat) (r : rat) :
  minor G 'K_n -> fractional_hadwiger_number G r -> n%:R <= r.
Proof.
move=> /minorRE[phi [ne con dis nb]] [_ H].
apply: (H n phi (fun _ => 1)); split => //; last by rewrite sumr_const card_ord.
move=> v; rewrite sumr_const -[X in _ <= X](mulr1n 1) ler_pMn2l ?ltr01 //.
by apply/card_le1_eqP => i j vi vj; apply: (@rmap_disjE _ _ phi v).
Qed.

(** [Bs] is a set of nonempty connected sets of vertices joined pairwise by an edge. *)
Let good (Bs : {set {set G}}) : bool :=
  [forall S in Bs, (S != set0) && connectedb S] &&
  [forall S in Bs, forall S' in Bs, (S != S') ==> neighbor S S'].

(** [X] is a weighting of the sets of [Bs] such that the sets containing any given vertex have
    total weight at most 1. *)
Let feasible (Bs : {set {set G}}) (X : {set G} -> rat) : Prop :=
  (forall S, 0 <= X S) /\ (forall v, \sum_(S in Bs | v \in S) X S <= 1).

Let family_of Bs X : good Bs -> feasible Bs X ->
  fractional_clique_minor (fun i : 'I_#|Bs| => enum_val i) (fun i => X (enum_val i))
    (\sum_(S in Bs) X S).
Proof.
case/andP => /forall_inP g1 /forall_inP g2 [X0 Xc]; split => //.
- by move=> i; have /andP[ne /connectedP co] := g1 _ (enum_valP i).
- move=> i j ij; have /forall_inP/(_ _ (enum_valP j))/implyP := g2 _ (enum_valP i); apply.
  by apply: contra ij => /eqP/enum_val_inj ->.
- by move=> v; rewrite -(big_enum_val_cond (A := mem Bs) (fun S => v \in S)); exact: Xc.
- by rewrite big_enum_val.
Qed.

(** Every graph has a fractional Hadwiger number: for each set [Bs] of possible branch sets,
    the linear program of the weights attains its maximum ([lp_max]); the largest of these
    maxima is the fractional Hadwiger number. *)
Lemma fractional_hadwiger_number_exists : exists r, fractional_hadwiger_number G r.
Proof.
pose F Bs r := exists2 X, feasible Bs X & r = \sum_(S in Bs) X S.
have [||r [[Bs gB [X fX ->]] M]] := @max_of_maxima _ _ good F; last first.
- exists (\sum_(S in Bs) X S); split; first by do 3 eexists; exact: family_of gB fX.
  move=> n B w r' [w0 Bc adj cov ->]; pose Bs' := [set B i | i : 'I_n].
  pose X' S := \sum_(i | B i == S) w i.
  have <- : \sum_(S in Bs') X' S = \sum_i w i.
    by rewrite [RHS](partition_big B (mem Bs')) //= => i _; exact: imset_f.
  apply: (M Bs'); last first.
    exists X' => //; split => [S|v]; first by apply: sumr_ge0 => i _.
    have Bi i : v \in B i -> (B i \in Bs') && (v \in B i) by move=> vi; rewrite imset_f.
    apply: le_trans (cov v); rewrite (partition_big B (fun S => (S \in Bs') && (v \in S)) Bi).
    apply: ler_sum => S /andP[_ vS]; rewrite le_eqVlt; apply/orP; left; apply/eqP/eq_bigl => i.
    by case: eqP => [->|_]; rewrite ?vS ?andbF.
  apply/andP; split; apply/forall_inP => _ /imsetP[i _ ->].
    by have [ne co] := Bc i; rewrite ne; apply/connectedP.
  apply/forall_inP => _ /imsetP[j _ ->]; apply/implyP => Bij; apply: adj.
  by apply: contra Bij => /eqP ->.
- by exists set0; apply/andP; split; apply/forall_inP => S; rewrite inE.
move=> Bs gB.
have [||X [[X0 Xc] opt]] := @lp_max rat G {set G} (fun v S => ((S \in Bs) && (v \in S))%:R)
  (fun _ => 1) (fun S => (S \in Bs)%:R).
- by exists (fun _ => 0); split => // v; rewrite big1 // => S _; rewrite mulr0.
- exists #|G|%:R => X [X0 Xc]; rewrite sum_indicator_mul.
  apply: fractional_clique_minor_le_card (family_of gB _); split => // v.
  by have := Xc v; rewrite sum_indicator_mul.
exists (\sum_(S in Bs) X S); split.
  by exists X => //; split => // v; have := Xc v; rewrite sum_indicator_mul.
move=> _ [Y [Y0 Yc] ->]; have := opt Y; rewrite !sum_indicator_mul; apply; split => // v.
by rewrite sum_indicator_mul; exact: Yc.
Qed.

End FractionalHadwiger.
