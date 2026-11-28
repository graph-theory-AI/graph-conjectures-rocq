(** * The tensor power trick for homomorphism counts

The homomorphisms from F to a tensor product G1 x G2 are the pairs of homomorphisms to G1 and to
G2, and the vertices and the ordered pairs of adjacent vertices of G1 x G2 are the pairs of those
of G1 and G2.  Hence an inequality a(G) <= c b(G) between such multiplicative quantities, for
every graph G and a constant c, applies to the tensor powers G^k: a(G)^k <= c b(G)^k for all k,
and gives a(G) <= b(G) (Bernoulli's inequality). *)

From GraphTheory Require Import digraph sgraph.
From mathcomp Require Import boot.
From GC.GraphLib Require Import misc homomorphism.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Homomorphisms *)

(** The homomorphisms from [F] to [X], whose number is [hom_count F X]. *)
Definition homs (F X : diGraph) : {set {ffun F -> X}} :=
  [set f : {ffun F -> X} | [forall x : F, [forall y : F, (x -- y) ==> (f x -- f y)]]].

Lemma homsP (F X : diGraph) (f : {ffun F -> X}) :
  reflect (forall x y : F, x -- y -> f x -- f y) (f \in homs F X).
Proof.
rewrite inE; apply: (iffP forallP) => [h x y | h x]; first exact: implyP (forallP (h x) y).
by apply/forallP => y; apply/implyP/h.
Qed.

Section Split.
Variables (F X Y : finType).

(** A map to [X * Y] is a pair of maps. *)
Definition ffun_split (f : {ffun F -> X * Y}) : {ffun F -> X} * {ffun F -> Y} :=
  ([ffun x => (f x).1], [ffun x => (f x).2]).

Definition ffun_pair (g : {ffun F -> X} * {ffun F -> Y}) : {ffun F -> X * Y} :=
  [ffun x => (g.1 x, g.2 x)].

Lemma ffun_splitK : cancel ffun_split ffun_pair.
Proof. by move=> f; apply/ffunP => x; rewrite !ffunE -surjective_pairing. Qed.

Lemma ffun_pairK : cancel ffun_pair ffun_split.
Proof. by move=> [g1 g2]; congr pair; apply/ffunP => x; rewrite !ffunE. Qed.

End Split.

(** ** Tensor products and powers *)

Section Tensor.
Variables (G1 G2 : sgraph).

Lemma card_tensor : #|tensor_product G1 G2| = #|G1| * #|G2|.
Proof. exact: card_prod. Qed.

Lemma num_edges_tensor :
  num_edges (tensor_product G1 G2) = num_edges G1 * num_edges G2.
Proof.
pose f (p : (G1 * G1) * (G2 * G2)) : (G1 * G2) * (G1 * G2) := ((p.1.1, p.2.1), (p.1.2, p.2.2)).
pose g (p : (G1 * G2) * (G1 * G2)) : (G1 * G1) * (G2 * G2) := ((p.1.1, p.2.1), (p.1.2, p.2.2)).
have fK : cancel f g by case=> [[? ?] [? ?]].
have gK : cancel g f by case=> [[? ?] [? ?]].
pose E (G : sgraph) := [set p : G * G | p.1 -- p.2].
have -> : num_edges G1 * num_edges G2 = #|f @: setX (E G1) (E G2)|.
  by rewrite (card_imset _ (can_inj fK)) cardsX !cardsE.
by rewrite (can2_imset_pre _ fK gK); apply: eq_card => -[[x1 x2] [y1 y2]]; rewrite !inE.
Qed.

Lemma hom_count_tensor (F : diGraph) :
  hom_count F (tensor_product G1 G2) = hom_count F G1 * hom_count F G2.
Proof.
rewrite /hom_count -[LHS](card_imset _ (can_inj (@ffun_splitK F G1 G2))) -cardsX.
rewrite (can2_imset_pre _ (@ffun_splitK F G1 G2) (@ffun_pairK F G1 G2)).
apply: eq_card => -[g1 g2]; rewrite inE in_setX.
apply/homsP/andP => [h | [/homsP h1 /homsP h2] x y xy].
  by split; apply/homsP => x y /h; rewrite !ffunE => /andP[].
by rewrite !ffunE; apply/andP; split; [exact: h1 | exact: h2].
Qed.

End Tensor.

(** The tensor power [G^(k+1)]. *)
Fixpoint tensor_power (G : sgraph) (k : nat) : sgraph :=
  if k is k'.+1 then tensor_product (tensor_power G k') G else G.

(** ** Amplification *)

(** Bernoulli's inequality, multiplied by [b ^ n.+1]. *)
Lemma bernoulli (b n : nat) : b ^ n * (b + n) <= b * b.+1 ^ n.
Proof.
elim: n => [|n IH]; first by rewrite !expn0 addn0 muln1 mul1n.
rewrite !expnS -mulnA mulnCA; apply: leq_trans (_ : b.+1 * (b ^ n * (b + n)) <= _).
  by rewrite [X in _ <= X]mulnCA leq_mul2l addnS mulnS mulSn leq_add2r leq_addr orbT.
by rewrite [X in _ <= X]mulnCA leq_mul2l IH orbT.
Qed.

Lemma amplify (a b c : nat) : (forall k, a ^ k.+1 <= c * b ^ k.+1) -> a <= b.
Proof.
move=> h; rewrite leqNgt; apply/negP => ba.
have [b0|b_gt0] := posnP b.
  by move: (h 0) ba; rewrite b0 muln0 expn1 leqn0 => /eqP ->.
set n := (c * b).+1.
have : b ^ n * (b + n) <= b ^ n * (c * b).
  apply: leq_trans (bernoulli b n) _; rewrite [X in _ <= X]mulnCA mulnA mulnC leq_pmul2r //.
  by rewrite (leq_trans _ (h (c * b))) // leq_exp2r.
by rewrite leq_pmul2l ?expn_gt0 ?b_gt0 // /n addnS ltnNge leq_addl.
Qed.

(** The tensor power trick: a constant factor [c] can be removed from a lower bound on the
    number of homomorphisms from [F] in terms of the numbers of vertices and edges. *)
Theorem tensor_power_trick (F : diGraph) (e v w c : nat) :
  (forall G : sgraph, num_edges G ^ e * #|G| ^ v <= c * (hom_count F G * #|G| ^ w)) ->
  forall G : sgraph, num_edges G ^ e * #|G| ^ v <= hom_count F G * #|G| ^ w.
Proof.
move=> hc G; apply: (@amplify _ _ c) => k; move: (hc (tensor_power G k)).
have pw (f : sgraph -> nat) : (forall G1 G2, f (tensor_product G1 G2) = f G1 * f G2) ->
    f (tensor_power G k) = f G ^ k.+1.
  by move=> fM; elim: k => [|k IH] /=; rewrite ?expn1 // fM IH -expnSr.
rewrite (pw _ num_edges_tensor) (pw _ card_tensor) (pw _ (fun G1 G2 => @hom_count_tensor G1 G2 F)).
by rewrite !(expnAC _ k.+1) -!expnMn.
Qed.
