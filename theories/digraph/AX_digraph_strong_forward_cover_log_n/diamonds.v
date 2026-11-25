(** * Strong digraphs without logarithmic forward covers

The diamond chain D_m has the vertices c_k, a_k, b_k and the arcs c_k -> a_k -> c_(k+1) and
c_k -> b_k -> c_(k+1), for k in Z_m.  It is strong and has 3m vertices.  We show that its
forward covers have at least m orders.

The twins a_i and b_i have c_i as only in-neighbour and c_(i+1) as only out-neighbour.  Hence a
forward path between them contains a forward path from c_(i+1) to c_i, which goes around the
cycle through all the c_k.  So c_i is the last of the c_k in the order, and this determines i:
an order makes a forward couple of at most one pair of twins.

The disproof comes from Graph-Theory-LLM-Proofs (attacks/2304.03567__04), where D_m has in
addition the arcs c_k -> c_(k+1).  It was formalized in graph-theory-rocq
(digraph-theory/theories/applications/forward_cover_disproof.v). *)

From GraphTheory Require Import digraph.
From GC.GraphLib Require Import digraph.
From GC.digraph.AX_digraph_strong_forward_cover_log_n Require main.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Abbreviation forward_arc := main.forward_arc.
Abbreviation forward_pair := main.forward_pair.
Abbreviation forward_cover := main.forward_cover.

(** A property preserved by the cyclic successor holds everywhere if it holds somewhere. *)
Lemma cyclic_ind m (P : 'I_m -> Prop) (i : 'I_m) :
  P i -> (forall k, P k -> P (ordS k)) -> forall k, P k.
Proof.
move=> Pi PS k; have Piter n : P (iter n (@ordS m) i) by elim: n => //= n; apply: PS.
have iterE n : iter n (@ordS m) i = (i + n) %% m :> nat.
  elim: n => [|n IH]; first by rewrite addn0 modn_small.
  by rewrite iterS /= IH -addn1 modnDml addn1 addnS.
suff <- : iter (k + (m - i)) (@ordS m) i = k by [].
by apply: ord_inj; rewrite iterE addnCA subnKC ?modnDr ?modn_small // ltnW.
Qed.

(** The rank does not decrease along the forward paths. *)
Lemma forward_leq (D : diGraph) (r : D -> nat) (u v : D) :
  connect (forward_arc r) u v -> r u <= r v.
Proof.
case/connectP => p up ->; elim: p u up => //= w p IH u /andP[/andP[_ uw] wp].
exact: leq_trans (ltnW uw) (IH w wp).
Qed.

Section DiamondChain.
Variable m : nat.

(** The vertex [inl k] is c_k, the vertices [inr (k, true)] and [inr (k, false)] are a_k, b_k. *)
Definition diamond_rel (u v : 'I_m + 'I_m * bool) : bool :=
  match u, v with
  | inl k, inr (l, _) => l == k
  | inr (k, _), inl l => l == ordS k
  | _, _ => false
  end.

Definition diamonds : diGraph := RelType diamond_rel.

Definition hub (k : 'I_m) : diamonds := inl k.
Definition twin (k : 'I_m) (b : bool) : diamonds := inr (k, b).

Lemma card_diamonds : #|diamonds| = 3 * m.
Proof. by rewrite card_sum card_prod card_bool card_ord mulnC. Qed.

Lemma hub_twin k b : hub k -- twin k b.
Proof. exact: eqxx. Qed.

Lemma twin_hub k b : twin k b -- hub (ordS k).
Proof. exact: eqxx. Qed.

Lemma hub_out k u : hub k -- u -> exists b, u = twin k b.
Proof. by case: u => [//|[l b] /eqP->]; exists b. Qed.

Lemma twin_out k b u : twin k b -- u -> u = hub (ordS k).
Proof. by case: u => [l /eqP->|]. Qed.

Lemma twin_in k b u : u -- twin k b -> u = hub k.
Proof. by case: u => [l /eqP->|[]]. Qed.

Lemma diamonds_strong : strongly_connected diamonds.
Proof.
have to_hub u : forall k, connect (--) u (hub k).
  have [i ui] : exists i, connect (--) u (hub i).
    case: u => [k|[k b]]; first by exists k; apply: connect0.
    by exists (ordS k); apply/connect1/twin_hub.
  apply: (cyclic_ind ui) => k /connect_trans; apply.
  exact: connect_trans (connect1 (hub_twin k true)) (connect1 (twin_hub k true)).
apply/forallP => u; apply/forallP => -[k|[k b]]; first exact: to_hub.
exact: connect_trans (to_hub u k) (connect1 (hub_twin k b)).
Qed.

Section Order.
Variable r : diamonds -> nat.

(** (a_i, b_i) or (b_i, a_i) is a forward couple. *)
Definition twin_pair (i : 'I_m) : bool := forward_pair r (twin i true) (twin i false).

(** A forward path from c_k to c_i with k <> i goes through c_(k+1). *)
Lemma forward_next k i :
  connect (forward_arc r) (hub k) (hub i) -> k != i ->
  connect (forward_arc r) (hub (ordS k)) (hub i).
Proof.
case/connectP => -[_ [->]|]; first by rewrite eqxx.
move=> u [|v p] /= /andP[/andP[/hub_out[b ->] _]] //= /andP[/andP[/twin_out-> _] hp] E _.
by apply/connectP; exists p.
Qed.

(** A forward path between a_i and b_i contains a forward path from c_(i+1) to c_i. *)
Lemma forward_hubs i : twin_pair i -> connect (forward_arc r) (hub (ordS i)) (hub i).
Proof.
suff twins b : connect (forward_arc r) (twin i b) (twin i (~~ b)) ->
    connect (forward_arc r) (hub (ordS i)) (hub i) by case/orP; apply: twins.
case/connectP => -[|u p] /=; first by case: b.
case/andP => /andP[/twin_out-> _]; case/lastP: p => [//|p v]; rewrite rcons_path last_rcons.
case/andP => hp /[swap] <- /andP[/twin_in/esym E _].
by apply/connectP; exists p.
Qed.

(** If (a_i, b_i) or (b_i, a_i) is a forward couple, then c_i is the last of the c_k. *)
Lemma hub_max i : twin_pair i -> forall k, r (hub k) <= r (hub i).
Proof.
move/forward_hubs => hi k; apply: forward_leq; move: k.
apply: (cyclic_ind hi) => k hk; have [->//|ki] := eqVneq k i.
exact: forward_next.
Qed.

Lemma twin_pair_inj i j : injective r -> twin_pair i -> twin_pair j -> i = j.
Proof.
move=> r_inj hi hj; suff /r_inj[] : r (hub i) = r (hub j) by [].
by apply: anti_leq; rewrite !hub_max.
Qed.

End Order.

(** Mapping an order to its forward pair of twins, if any, shows that m orders are needed. *)
Lemma forward_cover_diamonds (rs : seq {ffun diamonds -> nat}) :
  forward_cover rs -> m <= size rs.
Proof.
case=> /allP inj_rs cov.
pose covered_pair (r : {ffun diamonds -> nat}) := [pick i | twin_pair r i].
rewrite -(size_enum_ord m) -(size_map Some) -(size_map covered_pair rs).
apply: uniq_leq_size => [|_ /mapP[i _ ->]].
  by rewrite map_inj_uniq ?enum_uniq //; exact: Some_inj.
have /cov/hasP[r r_rs ri] : twin i true != twin i false by apply/eqP => -[].
apply/mapP; exists r => //; rewrite /covered_pair.
case: pickP => [j rj|/(_ i)]; last by rewrite /twin_pair ri.
by rewrite (twin_pair_inj (injectiveP _ (inj_rs r r_rs)) ri rj).
Qed.

End DiamondChain.

(** For p = 2c + n0 and m = 4^p, the number m of orders exceeds c (2p + 2) >= c log_2 (3m). *)
Theorem no_log_forward_cover : ~ main.AX_digraph_strong_forward_cover_log_n.
Proof.
case=> c [n0 cover]; pose p := c.*2 + n0; pose m := 2 ^ p.*2.
have ltm : p.+1 ^ 2 <= m by rewrite /m -muln2 expnM leq_exp2r // ltn_expl.
have [|rs [/forward_cover_diamonds le_rs]] := cover _ (diamonds_strong m); last first.
  rewrite card_diamonds => /(leq_trans le_rs); apply/negP; rewrite -ltnNge.
  have log_le : trunc_log 2 (3 * m) <= p.+1.*2.
    rewrite -[p.+1.*2](@trunc_expnK 2) // leq_trunc_log // doubleS !expnS mulnA.
    by rewrite leq_mul2r orbT.
  rewrite (leq_ltn_trans (leq_mul (leqnn c) log_le)) // -doubleMr doubleMl.
  by rewrite (leq_trans _ ltm) // -mulnn ltn_mul2r /= ltnS leq_addr.
rewrite card_diamonds (leq_trans _ (leq_pmull _ _)) // (leq_trans _ ltm) // -mulnn.
by rewrite (leq_trans _ (leq_pmull _ _)) // (leq_trans (leq_addl c.*2 _)).
Qed.
