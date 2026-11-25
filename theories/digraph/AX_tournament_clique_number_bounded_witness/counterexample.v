(** * Arbitrarily large tournaments that are minimal of clique number 3

Let n >= 3, and let T be the circulant tournament on the integers modulo 2n+1, with the arcs from x
to x+1, ..., x+n-1 and x+n+1.

- ω(T) >= 3.  Indeed, each vertex x dominates the directed triangle x+1, x+2, x+n+1.  Given an
  order on the vertices, let x be the last one.  Its triangle contains a backedge, which forms with
  x a triangle of the backedge graph.
- ω(A) <= 2 for each proper subtournament A.  Let v be a vertex that is not in A, and consider the
  order v+1, v+2, ..., v+2n.  Two vertices joined by a backedge are at distance at least n in this
  order, hence a clique of the backedge graph has at most one vertex among v+1, ..., v+n, and at
  most one among v+n+1, ..., v+2n.

Therefore, a subtournament of T of clique number at least 3 has 2n+1 vertices, which is not bounded
by ℓ(3).

The proof comes from Graph-Theory-LLM-Proofs (attacks/2310.04265__09).  Another proof was
formalized in graph-theory-rocq
(digraph-theory/theories/applications/question_5_9_resolution.v). *)

From GraphTheory Require Import digraph.
From mathcomp Require Import boot algebra zify.
From GC.GraphLib Require Import digraph.
From GC.digraph.AX_tournament_clique_number_bounded_witness Require main.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.

(** ** A lower bound on the clique number *)

(** If each vertex dominates a directed triangle, then the clique number is at least 3. *)
Lemma diclique_number_ge3 (D : diGraph) (x0 : D) :
  irreflexive (@edge_rel D) ->
  (forall v : D, exists a b c,
     [/\ v -- a, v -- b & v -- c] /\ [/\ a -- b, b -- c & c -- a]) ->
  2 < diclique_number D.
Proof.
move=> loopless tri; rewrite ltnNge; apply/negP => /diclique_number_leP[f [f_inj le2]].
have neq (u w : D) : u -- w -> u != w by apply: contraTneq => ->; rewrite loopless.
have [v _ v_last] := arg_maxnP f (isT : xpredT x0).
have [a [b [c [[va vb vc] [ab bc ca]]]]] := tri v.
suff [x [y [vx vy xy back]]] : exists x y, [/\ v -- x, v -- y, x -- y & f y < f x].
  suff : #|v |: [set x; y]| <= 2 by rewrite cardsU1 cards2 !inE negb_or !neq.
  apply: le2 => u w; rewrite !inE => /or3P[] /eqP-> /or3P[] /eqP-> //; rewrite ?ltnn // => lt.
  - by have := leq_trans lt (v_last x isT); rewrite ltnn.
  - by have := leq_trans lt (v_last y isT); rewrite ltnn.
  - by have := ltn_trans lt back; rewrite ltnn.
have [|le_ab] := ltnP (f b) (f a); first by exists a, b.
have [|le_bc] := ltnP (f c) (f b); first by exists b, c.
exists c, a; split=> //; rewrite ltn_neqAle (leq_trans le_ab le_bc) andbT.
by rewrite (inj_eq f_inj) eq_sym neq.
Qed.

(** ** The circulant tournaments *)

Section Circulant.
Variable n : nat.

Local Notation "'Z" := 'I_(n.*2.+1) (only parsing).

(** The vertices are the integers modulo 2n+1. *)
Definition circulant_tournament : diGraph :=
  DiGraph [rel x y : 'Z | let d : nat := (y - x)%R in (0 < d < n) || (d == n.+1)].

Local Abbreviation T := circulant_tournament.

(** Translations are automorphisms. *)
Lemma circulant_shift (v x y : 'Z) : ((x + v)%R : T) -- (y + v)%R = (x : T) -- y.
Proof.
rewrite -[LHS]/(let d : nat := (y + v - (x + v))%R in (0 < d < n) || (d == n.+1)).
by rewrite opprD addrACA subrr addr0.
Qed.

(** Arcs in terms of integers. *)
Lemma circulant_arcE (x y : 'Z) :
  (x : T) -- y = (x < y) && ((y - x < n) || (y - x == n.+1)) ||
                 (y < x) && ((x - y == n) || (n.+1 < x - y)).
Proof.
have lt_x := ltn_ord x; have lt_y := ltn_ord y; rewrite /edge_rel /= modnDmr.
have [le_xy|lt_yx] := leqP x y; last by rewrite modn_small; lia.
by rewrite (_ : y + _ = y - x + n.*2.+1) ?modnDr ?modn_small; lia.
Qed.

Lemma circulant_tournamentP : tournament T.
Proof.
split=> [x|x y]; rewrite !circulant_arcE; first by rewrite ltnn.
rewrite -[x == y](inj_eq (@ord_inj _)).
by have := ltn_ord (x : 'Z); have := ltn_ord (y : 'Z); lia.
Qed.

(** Each vertex v dominates the directed triangle v+1, v+2, v+n+1. *)
Lemma circulant_tournament_ge3 : 2 < n -> 2 < diclique_number T.
Proof.
move=> n_gt2; apply: diclique_number_ge3 (proj1 circulant_tournamentP) _ => [|v].
  exact: (ord0 : 'Z).
have val0 : (0%R : 'Z) = 0 :> nat by [].
exists (inord 1 + v : 'Z)%R, (inord 2 + v : 'Z)%R, (inord n.+1 + v : 'Z)%R.
by rewrite -{1 3 5}(@add0r 'Z v) !circulant_shift !circulant_arcE !inordK ?val0; do ?split; lia.
Qed.

(** In the order v+1, v+2, ..., v+2n, backward arcs have length at least n. *)
Lemma circulant_tournament_sub (S : {set T}) (v : 'Z) :
  (v : T) \notin S -> diclique_number (induced S) <= 2.
Proof.
move=> vS; apply/diclique_number_leP.
pose pos (x : induced S) : 'Z := (val x - v)%R.
have pos_inj : injective pos by move=> x y /addIr/val_inj.
exists pos; split=> [x y /val_inj/pos_inj //|K back].
have pos_gt0 x : 0 < pos x.
  rewrite lt0n -[0]/(val (0%R : 'Z)) val_eqE subr_eq0.
  by apply: contraNneq vS => <-; apply: valP.
have far x y : x \in K -> y \in K -> pos x < pos y -> pos x + n <= pos y.
  move=> xK yK lt; have := back x y xK yK lt.
  rewrite -[_ -- _]/((val y : T) -- val x) -(circulant_shift (- v)%R) circulant_arcE.
  by rewrite -/(pos x) -/(pos y); lia.
rewrite -card_bool; apply: (@leq_card_in _ _ (fun x => n < pos x)) => x y xK yK eq_half.
apply/pos_inj/ord_inj; have := far x y xK yK; have := far y x yK xK.
by have := ltn_ord (pos x); have := ltn_ord (pos y); have := pos_gt0 x; have := pos_gt0 y; lia.
Qed.

End Circulant.

(** ** Conclusion *)

Lemma diclique_numberE (D : diGraph) : main.diclique_number D = diclique_number D.
Proof. by []. Qed.

Lemma disproof : ~ main.AX_tournament_clique_number_bounded_witness.
Proof.
case=> ell witness; pose n := maxn 3 (ell 3); have n_gt2 : 2 < n by rewrite leq_max.
have [|S [S_small]] := witness _ 3 (circulant_tournamentP n).
  by rewrite diclique_numberE; apply: circulant_tournament_ge3.
have /set0Pn[v] : ~: S != set0.
  rewrite -card_gt0 cardsCs setCK subn_gt0 card_ord; apply: leq_ltn_trans S_small _.
  by rewrite /n; lia.
by rewrite inE diclique_numberE leqNgt ltnS => /circulant_tournament_sub->.
Qed.
