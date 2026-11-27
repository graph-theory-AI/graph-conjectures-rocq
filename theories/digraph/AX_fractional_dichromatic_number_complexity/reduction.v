(** * Correctness and size of the reduction D |-> R(D)

The proof comes from Graph-Theory-LLM-Proofs (attacks/1812.02420__02).  It was formalized
in graph-theory-rocq (digraph-theory/theories/applications/fractional_dichromatic). *)

From GraphTheory Require Import digraph.
From GC.GraphLib Require Import digraph.
From GC.digraph.AX_fractional_dichromatic_number_complexity Require main.
From mathcomp Require Import boot order ssralg ssrnum.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.Theory GRing.Theory Num.Theory.

Abbreviation two_layer := main.two_layer.
Abbreviation fractional_dicolorable := main.fractional_dicolorable.

(** The edges of R(D). *)
Lemma two_layerE (D : diGraph) (u v : D) (i j : bool) :
  ((u, i) : two_layer D) -- (v, j) = ((i == j) && (u -- v)) || ((u == v) && (i != j)).
Proof. by []. Qed.

(** ** Preliminaries on acyclic sets *)

(** A set inducing an acyclic digraph contains at most one end of each digon. *)
Lemma acyclic_induced_digon (D : diGraph) (A : {set D}) (u v : D) :
  u -- v -> v -- u -> acyclic (induced A) -> ~~ ((u \in A) && (v \in A)).
Proof.
move=> uv vu /acyclic_inducedP[phi inc]; apply/negP => /andP[uA vA].
by have := ltn_trans (inc u v uA vA uv) (inc v u vA uA vu); rewrite ltnn.
Qed.

(** 2-dicolourability as a partition into two sets inducing acyclic digraphs. *)
Lemma dicolorable2P (D : diGraph) :
  dicolorable D 2 <->
  exists C : {set D}, acyclic (induced C) /\ acyclic (induced (~: C)).
Proof.
split=> [[col ac]|[C [aC aC']]].
- exists [set v | col v == ord0]; split; first exact: ac.
  suff -> : ~: [set v | col v == ord0] = [set v | col v == ord_max] by exact: ac.
  by apply/setP => v; rewrite !inE; case: (col v) => [[|[|m]] lt_m].
- exists (fun v => if v \in C then ord0 else ord_max) => i.
  have [->|->] : i = ord0 \/ i = ord_max.
    by case: i => [[|[|m]] lt_m] //; [left|right]; apply: val_inj.
  + suff -> : [set v | (if v \in C then ord0 else ord_max) == ord0 :> 'I_2] = C by [].
    by apply/setP => v; rewrite inE; case: (v \in C).
  + suff -> : [set v | (if v \in C then ord0 else ord_max) == ord_max :> 'I_2] = ~: C by [].
    by apply/setP => v; rewrite !inE; case: (v \in C).
Qed.

(** ** Size *)

Lemma card_two_layer (D : diGraph) : #|two_layer D| = 2 * #|D|.
Proof. by rewrite /= card_prod card_bool mulnC. Qed.

(** The edges of R(D) are those inside a layer, and those of the digons. *)
Lemma num_edges_two_layer (D : diGraph) :
  num_edges (two_layer D) = 2 * num_edges D + 2 * #|D|.
Proof.
pose E := [set e : D * D | e.1 -- e.2].
pose f (q : D * D * bool) : two_layer D * two_layer D := ((q.1.1, q.2), (q.1.2, q.2)).
pose g (q : D * bool) : two_layer D * two_layer D := (q, (q.1, ~~ q.2)).
have f_inj : injective f by move=> [[a b] c] [[a' b'] c'] [-> -> ->].
have g_inj : injective g by move=> [a c] [a' c'] [-> ->].
have edgesE : [set e : two_layer D * two_layer D | e.1 -- e.2]
            = f @: setX E setT :|: g @: setT.
  apply/setP => -[[u i] [v j]]; rewrite in_set in_setU two_layerE; congr (_ || _).
  - apply/andP/imsetP => [[/eqP<- uv]|[[[a b] c]]].
      by exists ((u, v), i); rewrite // !inE /= uv.
    by rewrite !inE /= andbT => ab [-> -> -> ->]; rewrite eqxx.
  - apply/andP/imsetP => [[/eqP<- ij]|[[a c] _ [-> -> -> ->]]].
      by exists (u, i); rewrite ?inE // /g /=; case: i j ij => [] [].
    by rewrite eqxx; case: c.
have disj : f @: setX E setT :&: g @: setT = set0.
  apply/setP => e; rewrite !inE; apply/negP => /andP[/imsetP[q _ ->] /imsetP[[a c] _]].
  by case=> _ -> _; case: c.
have numE (G : diGraph) : num_edges G = #|[set e : G * G | e.1 -- e.2]|.
  by rewrite cardsE.
rewrite !numE edgesE cardsU disj cards0 subn0 !card_imset // cardsX !cardsT.
by rewrite card_prod card_bool -/E mulnC [#|D| * 2]mulnC.
Qed.

(** ** From a fractional dicolouring of R(D) to a 2-dicolouring of D *)

Local Open Scope ring_scope.

(** Let nonnegative weights on the sets of a family [P] have total at most 2 and cover both
    [a] and [b] with weight at least 1.  If no set of [P] contains both [a] and [b], then
    each set of [P] of positive weight contains exactly one of them. *)
Lemma forcing (R : realFieldType) (T : finType) (P : pred {set T}) (x : {set T} -> R)
    (a b : T) :
  (forall A, 0 <= x A) ->
  (forall A, P A -> ~~ ((a \in A) && (b \in A))) ->
  1 <= \sum_(A | P A && (a \in A)) x A ->
  1 <= \sum_(A | P A && (b \in A)) x A ->
  \sum_(A | P A) x A <= 2 ->
  forall A, P A -> 0 < x A -> (a \in A) (+) (b \in A).
Proof.
move=> x0 noab cova covb tot A PA xA; apply: contraT => nab.
have [aA bA] : a \notin A /\ b \notin A.
  by move: nab (noab A PA); case: (a \in A); case: (b \in A).
have cov : 2 <= \sum_(B | P B && (B != A)) x B.
  apply: (le_trans (lerD cova covb)).
  rewrite !big_mkcondr -big_split /=; apply: ler_sum => B PB.
  have [->|_] := eqVneq B A; first by rewrite (negPf aA) (negPf bA) addr0.
  by move: (noab B PB); case: (a \in B); case: (b \in B) => //= _;
    rewrite ?addr0 ?add0r.
move: tot; rewrite (bigD1 A) //= => tot.
by have := ltr_pwDl xA cov; rewrite ltNge tot.
Qed.

Theorem dicolorable_of_frac (R : realFieldType) (D : diGraph) :
  fractional_dicolorable (two_layer D) (2 : R) -> dicolorable D 2.
Proof.
case=> x [x0 cov tot]; apply/dicolorable2P.
have [v0 _|D0] := pickP (@predT D); last first.
  by exists set0; split; apply/acyclic_inducedP; exists (fun=> 0%N) => u; have := D0 u.
have [A acA xA] : exists2 A : {set two_layer D}, acyclic (induced A) & 0 < x A.
  apply/exists_inP; apply: contraT => /exists_inPn noA.
  have := cov (v0, true); rewrite big1 ?ler10 // => A /andP[acA _].
  by apply/eqP; rewrite eq_le x0 leNgt noA.
have digon (v : D) : ((v, true) \in A) = ((v, false) \notin A).
  have noab (B : {set two_layer D}) : acyclic (induced B) ->
      ~~ (((v, true) \in B) && ((v, false) \in B)).
    by apply: acyclic_induced_digon; rewrite two_layerE eqxx orbT.
  by have := forcing x0 noab (cov _) (cov _) tot acA xA; do 2 case: (_ \in A).
have /acyclic_inducedP[phi inc] := acA.
exists [set v | (v, false) \in A]; split; apply/acyclic_inducedP.
- exists (fun v => phi (v, false)) => u v; rewrite !inE => uA vA uv.
  by apply: inc; rewrite // two_layerE uv.
- exists (fun v => phi (v, true)) => u v; rewrite !inE -!digon => uA vA uv.
  by apply: inc; rewrite // two_layerE uv.
Qed.

(** ** From a 2-dicolouring of D to a fractional dicolouring of R(D) *)

(** The vertices of [C] in one layer and the other vertices of [D] in the other layer. *)
Definition layers (D : diGraph) (C : {set D}) : {set two_layer D} :=
  [set a | (a.1 \in C) (+) a.2].

Lemma acyclic_layers (D : diGraph) (C : {set D}) :
  acyclic (induced C) -> acyclic (induced (~: C)) -> acyclic (induced (layers C)).
Proof.
move=> /acyclic_inducedP[phi0 inc0] /acyclic_inducedP[phi1 inc1].
apply/acyclic_inducedP; exists (fun a => if a.2 then phi1 a.1 else phi0 a.1).
move=> [u i] [v j]; rewrite !inE two_layerE /= => uC vC.
case/orP => /andP[/eqP eij uv]; last first.
  by move: uC vC uv; rewrite eij; case: (v \in C); case: i; case: j.
by rewrite -{}eij in vC *; case: i uC vC; rewrite ?addbT ?addbF => uC vC;
  [apply: inc1|apply: inc0]; rewrite ?inE.
Qed.

Theorem frac_of_dicolorable (R : realFieldType) (D : diGraph) :
  dicolorable D 2 -> fractional_dicolorable (two_layer D) (2 : R).
Proof.
case/dicolorable2P => C [acC acC'].
have acA : main.acyclic (induced (layers C)) by apply: acyclic_layers.
have acB : main.acyclic (induced (layers (~: C))) by apply: acyclic_layers; rewrite ?setCK.
have sum1 (P : pred {set two_layer D}) A :
    \sum_(S | P S) (S == A)%:R = (P A)%:R :> R.
  have [PA|nPA] := boolP (P A).
    by rewrite (bigD1 A) //= eqxx big1 ?addr0 // => S /andP[_ /negPf->].
  by rewrite big1 // => S PS; case: eqP PS nPA => // -> ->.
exists (fun S => (S == layers C)%:R + (S == layers (~: C))%:R); split.
- by move=> S; rewrite addr_ge0 ?ler0n.
- case=> v i; rewrite big_split /= !sum1 acA acB !inE /=.
  by case: (v \in C); case: i; rewrite ?addr0 ?add0r.
- by rewrite big_split /= !sum1 acA acB.
Qed.

(** ** Main result *)

Theorem reduction : main.proxy_AX_fractional_dichromatic_number_complexity.
Proof.
move=> R D; split; last exact: num_edges_two_layer; last exact: card_two_layer.
by split; [apply: dicolorable_of_frac|apply: frac_of_dicolorable].
Qed.
