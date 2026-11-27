(** * Codes and claws of the Petersen graph

The vertices of the Petersen graph, the 2-subsets of {0,...,4}, are coded by 5-bit integers
([code]), with the codes of their neighbours ([nbr]), for finite checks by computation.  The
Petersen graph is triangle-free ([petersen_triangle_free]): there are no three pairwise
disjoint 2-subsets of a 5-element set.  Hence three pairwise adjacent edges of the Petersen graph
have a common end ([petersen_claw]).

This proof comes from graph-theory-rocq (cycle-theory/theories/conjectures/implications_U6.v). *)

From mathcomp Require Import boot.
From GC.cycle.OPG_petersen_coloring_bridgeless_cubic Require main.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Abbreviation petersenV := main.petersenV.
Abbreviation petersen_adj := main.petersen_adj.
Abbreviation petersen_edge := main.petersen_edge.
Abbreviation petersen_ends := main.petersen_ends.
Abbreviation petersen_edge_adj := main.petersen_edge_adj.
Abbreviation mutually_adjacent := main.mutually_adjacent.

Implicit Types (x y u w : petersenV) (q : petersen_edge).

Lemma petersen_adj_sym : symmetric petersen_adj.
Proof. by move=> x y; rewrite /petersen_adj disjoint_sym. Qed.

Lemma petersen_adj_neq x y : petersen_adj x y -> x != y.
Proof.
apply: contraTneq => ->; rewrite /petersen_adj -setI_eq0 setIid -card_gt0.
by rewrite (eqP (valP y)).
Qed.

Lemma petersen_triangle_free x y u :
  petersen_adj x y -> petersen_adj y u -> petersen_adj x u -> False.
Proof.
rewrite /petersen_adj => xy yu xu; move: (max_card (val x :|: val y :|: val u)).
rewrite !cardsU (disjoint_setI0 xy) setIUl (disjoint_setI0 xu) (disjoint_setI0 yu) setU0.
by rewrite cards0 !subn0 (eqP (valP x)) (eqP (valP y)) (eqP (valP u)) card_ord.
Qed.

(** The ends of an edge, from one of them. *)
Lemma petersen_ends_other q u :
  u \in petersen_ends q -> exists y, petersen_ends q = [set u; y] /\ petersen_adj u y.
Proof.
have hq := valP q; rewrite !inE => /orP[] /eqP ->; first by exists (val q).2.
exists (val q).1; split; last by rewrite petersen_adj_sym.
by apply/setP => t; rewrite !inE orbC.
Qed.

(** Three pairwise adjacent edges have a common end [p]; their other ends are distinct. *)
Lemma petersen_claw q1 q2 q3 : mutually_adjacent petersen_edge_adj q1 q2 q3 ->
  exists p y1 y2 y3,
    [/\ petersen_ends q1 = [set p; y1], petersen_ends q2 = [set p; y2],
        petersen_ends q3 = [set p; y3], [/\ petersen_adj p y1, petersen_adj p y2
        & petersen_adj p y3] & [/\ y1 != y2, y2 != y3 & y1 != y3]].
Proof.
rewrite /main.mutually_adjacent /main.petersen_edge_adj.
case/and3P => /andP[n12 /set0Pn[p /setIP[p1 p2]]] /andP[n23 /set0Pn[r /setIP[r2 r3]]].
move=> /andP[n13 /set0Pn[s /setIP[s1 s3]]].
have [p3|p3] := boolP (p \in petersen_ends q3).
  have [y1 [e1 a1]] := petersen_ends_other p1.
  have [y2 [e2 a2]] := petersen_ends_other p2.
  have [y3 [e3 a3]] := petersen_ends_other p3.
  exists p, y1, y2, y3; split => //.
  by split; [move: n12 | move: n23 | move: n13]; rewrite ?e1 ?e2 ?e3; apply: contra => /eqP ->.
exfalso.
(* otherwise the ends of [q1], [q2], [q3] form a triangle *)
have span q x z : x \in petersen_ends q -> z \in petersen_ends q -> x != z ->
    petersen_ends q = [set x; z] /\ petersen_adj x z.
  move=> xq zq xz; have [y [e a]] := petersen_ends_other xq.
  by move: zq; rewrite e !inE eq_sym (negbTE xz) => /= /eqP ->.
have ps : p != s by apply: contraNneq p3 => ->.
have pr : p != r by apply: contraNneq p3 => ->.
have [e1 a1] := span _ _ _ p1 s1 ps.
have [e2 a2] := span _ _ _ p2 r2 pr.
have sr : s != r by apply: contraNneq n12 => sr; rewrite e1 e2 sr.
have [_ a3] := span _ _ _ s3 r3 sr.
exact: petersen_triangle_free a1 a3 a2.
Qed.

(** ** Codes of the subsets of ['I_5] *)

(** The subset [X] of ['I_5] has the code [\sum_(i in X) 2 ^ i]; [bit k c] is the bit [k] of the
    code [c]. *)
Definition bit (k c : nat) : bool := odd (c %/ 2 ^ k).
Definition popc (c : nat) : nat := bit 0 c + bit 1 c + bit 2 c + bit 3 c + bit 4 c.
Definition code (X : {set 'I_5}) : nat := \sum_(i < 5) (i \in X) * 2 ^ i.
Definition enc (b0 b1 b2 b3 b4 : bool) : nat := b0 + b1 * 2 + b2 * 4 + b3 * 8 + b4 * 16.

Lemma sum5 (F : 'I_5 -> nat) :
  \sum_(i < 5) F i = F (inord 0) + F (inord 1) + F (inord 2) + F (inord 3) + F (inord 4).
Proof.
rewrite !big_ord_recr big_ord0 /= add0n.
by congr (_ + _ + _ + _ + _); congr F; apply: val_inj; rewrite /= inordK.
Qed.

Lemma codeE (X : {set 'I_5}) : code X =
  enc (inord 0 \in X) (inord 1 \in X) (inord 2 \in X) (inord 3 \in X) (inord 4 \in X).
Proof. by rewrite /code sum5 /enc !inordK // expn0 muln1 expn1. Qed.

Lemma enc_bits (b0 b1 b2 b3 b4 : bool) :
  [/\ bit 0 (enc b0 b1 b2 b3 b4) = b0, bit 1 (enc b0 b1 b2 b3 b4) = b1,
      bit 2 (enc b0 b1 b2 b3 b4) = b2, bit 3 (enc b0 b1 b2 b3 b4) = b3
    & bit 4 (enc b0 b1 b2 b3 b4) = b4].
Proof. by case: b0; case: b1; case: b2; case: b3; case: b4. Qed.

Lemma bit_code (X : {set 'I_5}) (i : 'I_5) : bit i (code X) = (i \in X).
Proof.
rewrite codeE -[i in RHS]inord_val.
have := enc_bits (inord 0 \in X) (inord 1 \in X) (inord 2 \in X) (inord 3 \in X) (inord 4 \in X).
by case=> h0 h1 h2 h3 h4; case: i => -[|[|[|[|[|k]]]]] hk.
Qed.

Lemma code_inj : injective code.
Proof. by move=> X Y h; apply/setP => i; rewrite -!bit_code h. Qed.

(** The codes of the 2-subsets. *)
Definition C2 : seq nat := [:: 3; 5; 6; 9; 10; 12; 17; 18; 20; 24].

Lemma code_C2 (X : {set 'I_5}) : #|X| = 2 -> code X \in C2.
Proof.
rewrite -sum1_card big_mkcond sum5 /= codeE.
by case: (_ \in X); case: (_ \in X); case: (_ \in X); case: (_ \in X); case: (_ \in X).
Qed.

Lemma card_bits (c : nat) : #|[set i : 'I_5 | bit i c]| = popc c.
Proof. by rewrite -sum1_card big_mkcond sum5 /= !inE !inordK. Qed.

Definition disj (c d : nat) : bool := all (fun k => ~~ (bit k c && bit k d)) (iota 0 5).

Lemma disj_code (X Y : {set 'I_5}) : [disjoint X & Y] -> disj (code X) (code Y).
Proof.
move=> h; apply/allP => k; rewrite mem_iota => /andP[_ hk].
rewrite -(inordK (hk : k < 5)) !bit_code.
by case xk : (inord k \in X) => //=; rewrite (disjointFr h xk).
Qed.

(** The codes of the three neighbours of each vertex. *)
Definition nbr (c : nat) : seq nat :=
  match c with
  | 3 => [:: 12; 20; 24] | 5 => [:: 10; 18; 24] | 6 => [:: 9; 17; 24]
  | 9 => [:: 6; 18; 20] | 10 => [:: 5; 17; 20] | 12 => [:: 3; 17; 18]
  | 17 => [:: 6; 10; 12] | 18 => [:: 5; 9; 12] | 20 => [:: 3; 9; 10]
  | 24 => [:: 3; 5; 6] | _ => [::]
  end.

Lemma nbr_check : all (fun c => all (fun d => disj c d ==> (d \in nbr c)) C2) C2.
Proof. by compute. Qed.

Lemma code_V (p : petersenV) : code (val p) \in C2.
Proof. exact: code_C2 (eqP (valP p)). Qed.

Lemma code_nbr (p y : petersenV) : petersen_adj p y -> code (val y) \in nbr (code (val p)).
Proof.
move=> a; move/allP: nbr_check => /(_ _ (code_V p)) /allP /(_ _ (code_V y)) /implyP.
by apply; apply: disj_code a.
Qed.
