(** * There is no directed Kneser graph K(5,3)

Suppose that R is the arc relation of a directed Kneser graph K(5,3).  Any two triples of [5]
intersect, hence induce an acyclic subdigraph: there is no loop and no digon.  Consider the four
triples T_i that avoid a given element 0, T_i being the complement of {0,i}.

- T_i and T_j, for i <> j, are joined by an arc: the triples T_i, T_j and {0,i,j} have no common
  element, hence they contain a directed cycle, which is a triangle since there is no digon.
- Any three of the T_i have a common element, hence do not form a directed triangle.

Therefore, the T_i induce a transitive tournament, which is acyclic, but they have no common
element, a contradiction.

The proof comes from Graph-Theory-LLM-Proofs (attacks/1812.02420__03).  It was formalized
in graph-theory-rocq (digraph-theory/theories/applications/directed_kneser_nonexistence.v), and
simplified here. *)

From GraphTheory Require Import digraph.
From mathcomp Require Import boot.
From GC.GraphLib Require Import digraph.
From GC.digraph.AX_directed_kneser_graphs_existence Require main.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Abbreviation bsubset := main.bsubset.
Abbreviation kneser_digraph := main.kneser_digraph.
Abbreviation directed_kneser_property := main.directed_kneser_property.

(** ** Oriented graphs *)

Lemma oriented_irreflexive (D : diGraph) : oriented D -> irreflexive (@edge_rel D).
Proof. by move=> orD u; apply/negP => uu; have := orD _ _ uu; rewrite uu. Qed.

(** In an oriented graph, three vertices, two of which are not adjacent, induce an acyclic
    digraph. *)
Lemma acyclic_induced3 (D : diGraph) (x y z : D) :
  oriented D -> ~~ (x -- y) -> ~~ (y -- x) -> acyclic (induced [set x; y; z]).
Proof.
move=> orD nxy nyx; have loopless := oriented_irreflexive orD.
apply/acyclic_inducedP; exists (fun u => if u -- z then 0 else if u == z then 1 else 2) => u v.
rewrite !inE => /orP[uxy|/eqP->]; last first.
  by rewrite eqxx loopless => _ zv; rewrite (negbTE (orD _ _ zv)) -[v == z]negbK;
     case: eqP zv => // ->; rewrite loopless.
case/orP=> [vxy uv|/eqP-> -> //]; last by rewrite loopless eqxx.
by move: uv; case/orP: uxy => /eqP->; case/orP: vxy => /eqP->;
   rewrite ?loopless ?(negbTE nxy) ?(negbTE nyx).
Qed.

(** ** The triples of a set of five elements *)

Section Kneser53.
Variable R : rel (bsubset 5 3).
Hypothesis KP : directed_kneser_property R.

Let D := kneser_digraph R.
Let triple (A : D) : {set 'I_5} := sval A.
Let vertex (S : {set 'I_5}) (S3 : #|S| == 3) : D := Sub S S3.

(** A family of triples with a common element induces an acyclic subdigraph. *)
Lemma acyclic_common (i : 'I_5) (X : {set D}) :
  (forall A, A \in X -> i \in triple A) -> acyclic (induced X).
Proof. by move=> iX; apply/(KP X).2; exists i. Qed.

(** There is no loop and no digon. *)
Lemma oriented_kneser : oriented D.
Proof.
move=> A B AB; apply/negP => BA.
have /set0Pn[i /setIP[iA iB]] : triple A :&: triple B != set0.
  rewrite -card_gt0 -(ltn_add2l #|triple A :|: triple B|) addn0 cardsUI.
  rewrite (eqP (svalP A)) (eqP (svalP B)).
  by apply: leq_ltn_trans (max_card _) _; rewrite card_ord.
have /acyclic_inducedP[phi inc] : acyclic (induced [set A; B]).
  by apply: (acyclic_common (i := i)) => C /set2P[]->.
by have := ltn_trans (inc _ _ (set21 A B) (set22 A B) AB) (inc _ _ (set22 A B) (set21 A B) BA);
   rewrite ltnn.
Qed.

(** The triple T_i, where the elements other than 0 are denoted by [lift ord0 i]. *)
Lemma card_T (i : 'I_4) : #|~: [set ord0; lift ord0 i]| == 3.
Proof. by rewrite cardsCs setCK cards2 neq_lift card_ord. Qed.

Definition T (i : 'I_4) : D := vertex (card_T i).

Lemma in_T (i : 'I_4) (j : 'I_5) : (j \in triple (T i)) = (j != ord0) && (j != lift ord0 i).
Proof. by rewrite !inE negb_or. Qed.

Lemma T_total (i j : 'I_4) : i != j -> (T i -- T j) || (T j -- T i).
Proof.
move=> ij; apply: contraT; rewrite negb_or => /andP[nij nji].
have C3 : #|ord0 |: [set lift ord0 i; lift ord0 j]| == 3.
  by rewrite cardsU1 cards2 !inE (inj_eq lift_inj) ij !(negbTE (neq_lift _ _)).
have /(KP _).1[k kX] := acyclic_induced3 (vertex C3) oriented_kneser nij nji.
have : k \in triple (vertex C3) by apply: kX; rewrite !inE eqxx orbT.
have := kX (T j); have := kX (T i); rewrite !in_T !inE !eqxx !orbT.
by move=> /(_ isT)/andP[/negbTE-> /negbTE->] /(_ isT)/andP[_ /negbTE->].
Qed.

Lemma T_acyclic3 (i j k : 'I_4) : acyclic (induced [set T i; T j; T k]).
Proof.
have /card_gt0P[l] : 0 < #|[predC [:: i; j; k]]|.
  rewrite -(ltn_add2l #|[:: i; j; k]|) addn0 cardC card_ord ltnS; exact: card_size.
rewrite !inE !negb_or => /and3P[li lj lk].
apply: (acyclic_common (i := lift ord0 l)) => A; rewrite !inE => /orP[/orP[]|] /eqP->;
  by rewrite in_T eq_sym neq_lift (inj_eq lift_inj).
Qed.

Lemma T_transitive (i j k : 'I_4) : T i -- T j -> T j -- T k -> T i -- T k.
Proof.
move=> ij jk; have [ik|ik] := eqVneq i k.
  by rewrite -ik in jk; have := oriented_kneser ij; rewrite jk.
have /orP[//|ki] := T_total ik.
have /acyclic_inducedP[phi inc] := T_acyclic3 i j k.
suff: phi (T i) < phi (T i) by rewrite ltnn.
by apply: (ltn_trans (inc _ _ _ _ ij) (ltn_trans (inc _ _ _ _ jk) (inc _ _ _ _ ki)));
   rewrite !inE eqxx ?orbT.
Qed.

Lemma no_kneser53 : False.
Proof.
have /(KP _).1[j jT] : acyclic (induced [set T i | i : 'I_4]).
  apply/acyclic_inducedP; exists (fun A : D => #|[set i | T i -- A]|).
  move=> _ _ /imsetP[i _ ->] /imsetP[k _ ->] ik.
  apply/proper_card/properP; split.
    by apply/subsetP => l; rewrite !inE => /T_transitive/(_ ik).
  by exists i; rewrite !inE // (oriented_irreflexive oriented_kneser).
have {}jT i : (j != ord0) && (j != lift ord0 i) by rewrite -in_T; apply/jT/imset_f.
by have := jT ord0; case: (unliftP ord0 j) jT => [i ->|-> //] /(_ i); rewrite eqxx andbF.
Qed.

End Kneser53.

Theorem no_directed_kneser : ~ main.AX_directed_kneser_graphs_existence.
Proof. by move=> ex; have [R KP] := ex 5 3 isT isT; apply: no_kneser53 KP. Qed.
