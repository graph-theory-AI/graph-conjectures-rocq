(** * Labels of the edges of the Petersen graph, pulled back along a Petersen colouring

A labelling of the edges of the Petersen graph is given by a table [t] on the codes of their ends
(see [code]): the label of the edge between the vertices of codes [a < b] is [t a b].  Finite
checks on the codes then give properties of the labels of all edges ([edge_checkP]) and of the
labels of the three edges of every claw ([claw_checkP]): three pairwise adjacent edges of the
Petersen graph have a common end ([petersen_claw]).

A Petersen colouring [f] of a loopless cubic graph [G] maps the three edges at a vertex [v] to a
claw.  Hence, for a set [P] of edges of the Petersen graph, the degree of [v] in the preimage of
[P] by [f] is the number of edges of a claw in [P] ([pull_claw]). *)

From GraphTheory Require Import mgraph.
From mathcomp Require Import boot.
From GC.GraphLib Require Import misc even_subgraph.
From GC.cycle.OPG_petersen_coloring_bridgeless_cubic Require Import petersen_claws.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Finite checks on the codes *)

Section Labels.
Variable t : nat -> nat -> nat.

(** The label of the edge between the vertices of codes [c] and [d]. *)
Definition lab (c d : nat) : nat := t (minn c d) (maxn c d).

(** The label of an edge. *)
Definition plabel (q : petersen_edge) : nat := lab (code (val (val q).1)) (code (val (val q).2)).

Lemma plabel_ends (q : petersen_edge) (p y : petersenV) :
  petersen_ends q = [set p; y] -> plabel q = lab (code (val p)) (code (val y)).
Proof.
move=> e; have n := petersen_adj_neq (valP q).
have : (val q).1 \in [set p; y] by rewrite -e !inE eqxx.
have : (val q).2 \in [set p; y] by rewrite -e !inE eqxx orbT.
rewrite /plabel !inE => /orP[] /eqP h2 /orP[] /eqP h1.
all: rewrite h1 h2 ?eqxx // in n *; by rewrite /lab minnC maxnC.
Qed.

(** [R] holds for the labels of all edges. *)
Definition edge_check (R : pred nat) : bool := all (fun c => all (fun d => R (lab c d)) (nbr c)) C2.

Lemma edge_checkP R : edge_check R -> forall q, R (plabel q).
Proof.
move=> /allP h q; move: h => /(_ _ (code_V (val q).1)) /allP; apply.
exact: code_nbr (valP q).
Qed.

(** [R] holds for the labels of the three edges of every claw. *)
Definition claw_check (R : nat -> nat -> nat -> bool) : bool :=
  all (fun c => all (fun d1 => all (fun d2 => all (fun d3 =>
      [&& d1 != d2, d2 != d3 & d1 != d3] ==> R (lab c d1) (lab c d2) (lab c d3))
    (nbr c)) (nbr c)) (nbr c)) C2.

Lemma claw_checkP R : claw_check R -> forall q1 q2 q3,
  mutually_adjacent petersen_edge_adj q1 q2 q3 -> R (plabel q1) (plabel q2) (plabel q3).
Proof.
move=> h q1 q2 q3 /petersen_claw [p [y1 [y2 [y3 [e1 e2 e3 [a1 a2 a3] [d12 d23 d13]]]]]].
rewrite (plabel_ends e1) (plabel_ends e2) (plabel_ends e3).
have d (y y' : petersenV) : y != y' -> code (val y) != code (val y').
  by apply: contraNneq => /code_inj/val_inj ->.
move/allP: h => /(_ _ (code_V p)) /allP /(_ _ (code_nbr a1)) /allP
  /(_ _ (code_nbr a2)) /allP /(_ _ (code_nbr a3)).
by rewrite (d _ _ d12) (d _ _ d23) (d _ _ d13) => /implyP; apply.
Qed.

End Labels.

(** ** Pulling back sets of edges along a Petersen colouring *)

Section Pullback.
Variables (G : mgraph) (f : edge G -> petersen_edge).
Hypothesis Gc : loopless_cubic G.
Hypothesis fc : forall e1 e2 e3 : edge G, mutually_adjacent (@mline_rel G) e1 e2 e3 ->
  mutually_adjacent petersen_edge_adj (f e1) (f e2) (f e3).

(** A property [Q] of the number of edges of a claw in [P] holds for the degrees in the preimage
    of [P]. *)
Lemma pull_claw (P : pred petersen_edge) (Q : nat -> Prop) (v : G) :
  (forall q1 q2 q3, mutually_adjacent petersen_edge_adj q1 q2 q3 -> Q (P q1 + P q2 + P q3)) ->
  Q (mdeg_in [set e | P (f e)] v).
Proof.
move=> hQ; case: Gc => ll cub; rewrite mdeg_in_loopless //.
have /card_gt0P[e1 e1v] : 0 < #|edges_at v| by rewrite cub.
have /cards2P[e2 [e3 [n23 E]]] : #|edges_at v :\ e1| == 2.
  by move: (cub v); rewrite (cardsD1 e1) e1v add1n => -[->].
have : e2 \in edges_at v :\ e1 by rewrite E !inE eqxx.
have : e3 \in edges_at v :\ e1 by rewrite E !inE eqxx orbT.
rewrite !inE => /andP[n13 e3v] /andP[n12 e2v].
have adj a b : incident v a -> incident v b -> a != b -> mline_rel a b.
  by move=> av bv ab; rewrite /mline_rel ab /=; apply/existsP; exists v; rewrite av bv.
have e1v' : incident v e1 by rewrite inE in e1v.
have ma : mutually_adjacent (@mline_rel G) e1 e2 e3.
  by apply/and3P; split; apply: adj => //; rewrite eq_sym.
have := hQ _ _ _ (fc ma); rewrite -(setD1K e1v) E setIC -sum1_card.
under eq_bigl => e do rewrite in_setI.
rewrite big_mkcondr /= big_setU1 ?inE ?negb_or ?(eq_sym e1) ?n12 ?n13 //= big_setU1 ?inE //=.
by rewrite big_set1 !inE addnA.
Qed.

End Pullback.
