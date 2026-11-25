(** * The complement of the circulant graph C_13(1, 5)

    This graph with 13 vertices has no clique of size 5 and no stable set of size 3.  Hence its
    cocolourings (whose classes are cliques or stable sets) have at least 13 / 4 colours, and its
    proper colourings at least 13 / 2.  It has a cocolouring with 4 colours, one of whose classes
    is stable, and a proper colouring with 7 colours. *)

From GraphTheory Require Import preliminaries digraph sgraph dom coloring.
From mathcomp Require Import boot.
From GC.GraphLib Require Import misc chromatic.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** [x < y], and their difference is neither 1, 5, -5 nor -1 modulo 13. *)
Definition seed_rel : rel nat := fun x y => (x < y) && (y - x \notin [:: 1; 5; 8; 12]).

Definition seed : sgraph := sgraph_of_rel (fun x y : 'I_13 => seed_rel x y).

(** ** Cliques and stable sets *)

(** No sequence of [n] elements of [s] is such that each one is in relation [r] with the next
    ones. *)
Fixpoint no_clique (r : rel nat) (n : nat) (s : seq nat) : bool :=
  if n is n'.+1 then all (fun x => no_clique r n' [seq y <- s | r x y]) s else false.

Lemma no_cliqueP (r : rel nat) (m n : nat) (s : seq nat) (K : {set 'I_m}) :
  no_clique r n s -> {in K, forall x : 'I_m, val x \in s} ->
  {in K &, forall x y : 'I_m, x != y -> r x y} -> #|K| < n.
Proof.
elim: n s K => // n IHn s K /allP no_s sK rK; have [->|[x xK]] := set_0Vmem K.
  by rewrite cards0.
rewrite (cardsD1 x) xK ltnS.
apply: (IHn _ (K :\ x) (no_s _ (sK _ xK))) => [y|y z] /setD1P[yx yK].
- by rewrite mem_filter sK // rK // eq_sym.
- by case/setD1P => _; apply: rK.
Qed.

Lemma mem_iota_ord (n : nat) (x : 'I_n) : val x \in iota 0 n.
Proof. by rewrite mem_iota ltn_ord. Qed.

Lemma seed_clique (K : {set seed}) : clique K -> #|K| <= 4.
Proof.
move=> clK; rewrite -ltnS; apply: (no_cliqueP (r := sc seed_rel) (s := iota 0 13)).
- by vm_compute.
- by move=> x _; apply: mem_iota_ord.
- by move=> x y xK yK neq_xy; have := clK x y xK yK neq_xy; rewrite /edge_rel /= neq_xy.
Qed.

Lemma seed_stable (S : {set seed}) : stable S -> #|S| <= 2.
Proof.
move=> /stableP stS; rewrite -ltnS.
apply: (no_cliqueP (r := fun x y => (x != y) && ~~ sc seed_rel x y) (s := iota 0 13)).
- by vm_compute.
- by move=> x _; apply: mem_iota_ord.
- move=> x y xS yS neq_xy; have := stS x y xS yS; rewrite /edge_rel /= neq_xy => ->.
  by rewrite andbT.
Qed.

Lemma omega_seed : ω([set: seed]) <= 4.
Proof. by case: omegaP => K /maxclique_clique/seed_clique. Qed.

(** ** Colourings *)

Lemma card_le_classes (T : finType) (k b : nat) (f : T -> 'I_k) :
  (forall i, #|[set x | f x == i]| <= b) -> #|T| <= k * b.
Proof.
move=> le_b; rewrite -sum1_card (partition_big f predT) //=.
rewrite -[k in k * b]card_ord -sum_nat_const; apply: leq_sum => i _.
by rewrite sum1dep_card.
Qed.

Lemma cocolorable_seed_ge (k : nat) : cocolorable seed k -> 4 <= k.
Proof.
move=> [col hom]; suff /card_le_classes: forall i, #|[set v | col v == i]| <= 4.
  by rewrite card_ord (ltn_mul2r 4 3).
by move=> i; have [/seed_clique|/seed_stable/leq_trans->] := hom i.
Qed.

(** The classes {8, 9} (stable), {0, 2, 4, 6}, {1, 5, 7, 11} and {3, 10, 12} (cliques). *)
Lemma seed_cocoloring :
  exists col : seed -> 'I_4,
    (forall i, clique [set v | col v == i] \/ stable [set v | col v == i]) /\
    stable [set v | col v == ord0].
Proof.
pose c x := nth 0 [:: 1; 2; 1; 3; 1; 2; 1; 2; 0; 0; 3; 2; 3] x %% 4.
have lt4 x : c x < 4 by rewrite ltn_mod.
pose col (x : seed) := Ordinal (lt4 x).
have check : all (fun x => all (fun y => (x != y) && (c x == c y) ==>
    (sc seed_rel x y == (c x != 0))) (iota 0 13)) (iota 0 13) by vm_compute.
have colP (x y : seed) : x != y -> col x = col y -> x -- y = (col x != ord0).
  move=> neq_xy [] /eqP eq_xy; have := allP (allP check x (mem_iota_ord x)) y (mem_iota_ord y).
  rewrite eq_xy andbT => /implyP/(_ neq_xy)/eqP <-.
  by rewrite /edge_rel /= neq_xy.
have st0 : stable [set v | col v == ord0].
  apply/stableP => x y; rewrite !inE => /eqP cx /eqP cy; have [->|neq_xy] := eqVneq x y.
    by rewrite sg_irrefl.
  by rewrite colP ?cx ?cy.
exists col; split=> // i; have [->|i0] := eqVneq i ord0; [by right|left].
by move=> x y; rewrite !inE => /eqP cx /eqP cy neq_xy; rewrite colP ?cx ?cy.
Qed.

Lemma chi_seed : χ([set: seed]) = 7.
Proof.
apply/eqP; rewrite eqn_leq; apply/andP; split.
- have lt7 x : x %/ 2 %% 7 < 7 by rewrite ltn_mod.
  apply/chi_leP; exists (fun x : seed => Ordinal (lt7 x)); apply/proper_coloringP => x y.
  have check : all (fun x => all (fun y => sc seed_rel x y ==> (x %/ 2 %% 7 != y %/ 2 %% 7))
    (iota 0 13)) (iota 0 13) by vm_compute.
  move=> /andP[_]; apply/implyP.
  exact: allP (allP check x (mem_iota_ord x)) y (mem_iota_ord y).
- have /chi_leP[col /proper_coloringP pcol] := leqnn χ([set: seed]).
  suff /card_le_classes : forall i, #|[set v | col v == i]| <= 2.
    by rewrite card_ord (ltn_mul2r 2 6).
  move=> i; apply/seed_stable/stableP => x y; rewrite !inE => /eqP cx /eqP cy.
  by apply/negP => /pcol; rewrite cx cy eqxx.
Qed.
