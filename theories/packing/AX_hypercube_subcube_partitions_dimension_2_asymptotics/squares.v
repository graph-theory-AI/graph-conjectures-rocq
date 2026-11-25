(** * Subcubes and squares of the hypercube

A subcube is given by one of its vertices and by the set of its free coordinates.  A square is a
subcube of dimension 2.  Each square of Q_m has 4 vertices, each vertex is in C(m,2) squares,
and there are 2^(m-2) C(m,2) squares. *)

From GraphTheory Require Import digraph sgraph.
From GC.GraphLib Require hypergraph packing.
From GC.packing.AX_hypercube_subcube_partitions_dimension_2_asymptotics Require main.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Abbreviation hypercube := main.hypercube.
Abbreviation subcube := main.subcube.
Abbreviation subcube_dim := main.subcube_dim.
Abbreviation is_subcube_of_dim := main.is_subcube_of_dim.
Abbreviation square_partition_count := main.square_partition_count.

Lemma card_hypercube m : #|hypercube m| = 2 ^ m.
Proof. by rewrite card_tuple card_bool. Qed.

(** Double counting of the incidences between [E] and [X]. *)
Lemma sum_degree (T : finType) (E : {set {set T}}) (X : {set T}) :
  \sum_(x in X) #|[set S in E | x \in S]| = \sum_(S in E) #|S :&: X|.
Proof.
under eq_bigr do rewrite -sum1dep_card big_mkcondr.
rewrite exchange_big; apply: eq_bigr => S _.
by rewrite -big_mkcondr sum1dep_card; apply: eq_card => x; rewrite !inE andbC.
Qed.

(** ** Squares *)

Section Squares.
Variable m : nat.
Implicit Types (x y : hypercube m) (F : {set 'I_m}) (S : {set hypercube m}).

(** The subcube containing [x] whose set of free coordinates is [F]. *)
Definition face x F : {set hypercube m} :=
  subcube [ffun i => if i \in F then None else Some (tnth x i)].

Definition squares : {set {set hypercube m}} := [set S | is_subcube_of_dim 2 S].

Lemma faceP x F y : reflect (forall i, i \notin F -> tnth y i = tnth x i) (y \in face x F).
Proof.
rewrite inE; apply: (iffP forallP) => h i; have := h i; rewrite ffunE.
  by move=> /[swap] /negPf-> /eqP.
by case: (i \in F) => //= ->.
Qed.

Lemma face_id x F : x \in face x F.
Proof. exact/faceP. Qed.

Lemma face_dim x F : subcube_dim [ffun i => if i \in F then None else Some (tnth x i)] = #|F|.
Proof. by apply: eq_card => i; rewrite inE ffunE; case: (i \in F). Qed.

Lemma face_square x F : #|F| = 2 -> face x F \in squares.
Proof.
move=> F2; rewrite inE; apply/existsP; eexists; apply/andP.
by split; [exact: eqxx|rewrite face_dim F2].
Qed.

Lemma squareP x S : S \in squares -> x \in S -> exists2 F : {set 'I_m}, #|F| = 2 & S = face x F.
Proof.
rewrite inE => /existsP[c /andP[/eqP-> /eqP c2]] xc; exists [set i | c i == None] => //.
apply/setP => y; rewrite !inE in xc *; apply: eq_forallb => i; have := forallP xc i.
by rewrite ffunE inE; case: (c i) => //= b /eqP->.
Qed.

Lemma card_square S : S \in squares -> #|S| = 4.
Proof.
rewrite inE => /existsP[c /andP[/eqP-> /eqP c2]].
by rewrite (packing.card_subcube c : #|subcube c| = 2 ^ subcube_dim c) c2.
Qed.

Lemma square_neq0 S : S \in squares -> S != set0.
Proof. by move/card_square => S4; rewrite -card_gt0 S4. Qed.

Lemma face_inj x : injective (face x).
Proof.
have face_flip F i : ([tuple tnth x j (+) (j == i) | j < m] \in face x F) = (i \in F).
  apply/faceP/idP => [h|iF j jF].
    by apply: contraT => /h/eqP; rewrite tnth_mktuple eqxx; case: (tnth x i).
  by rewrite tnth_mktuple; case: eqP jF => [->|]; rewrite ?iF ?addbF.
by move=> F G FG; apply/setP => i; rewrite -!face_flip FG.
Qed.

(** The degree of a vertex is C(m,2). *)
Lemma degree_squares x : #|[set S in squares | x \in S]| = 'C(m, 2).
Proof.
have -> : [set S in squares | x \in S] = face x @: [set F : {set 'I_m} | #|F| == 2].
  apply/setP => S; rewrite inE; apply/andP/imsetP => [[Ssq xS]|[F]].
    by have [F F2 ->] := squareP Ssq xS; exists F; rewrite // inE F2.
  by rewrite inE => /eqP F2 ->; rewrite face_square ?face_id.
by rewrite (card_imset _ (@face_inj x)) card_draws card_ord.
Qed.

Lemma card_squares : #|squares| * 4 = 2 ^ m * 'C(m, 2).
Proof.
rewrite -card_hypercube -cardsT -!sum_nat_const.
under [RHS]eq_bigr => x _ do rewrite -(degree_squares x); rewrite sum_degree.
by apply: eq_bigr => S Ssq; rewrite setIT card_square.
Qed.

(** A square meets at most 4 C(m,2) squares. *)
Lemma card_squares_meet S : S \in squares ->
  #|[set S' in squares | S' :&: S != set0]| <= 4 * 'C(m, 2).
Proof.
move=> Ssq; rewrite -(card_square Ssq) -sum_nat_const.
under eq_bigr => x _ do rewrite -(degree_squares x); rewrite sum_degree.
rewrite -sum1dep_card big_mkcondr; apply: leq_sum => S' _.
by rewrite -card_gt0; case: #|_|.
Qed.

(** ** Matchings *)

(** The sets of pairwise disjoint squares. *)
Definition matchings : {set {set {set hypercube m}}} :=
  [set M : {set {set hypercube m}} | (M \subset squares) && trivIset M].

Lemma matchingP {M} : reflect (hypergraph.hg_matching M squares) (M \in matchings).
Proof. by rewrite inE; apply: andP. Qed.

Lemma matching_sub {M S} : M \in matchings -> S \in M -> S \in squares.
Proof. by case/matchingP => /subsetP sub _; apply: sub. Qed.

Lemma card_matching M : M \in matchings -> #|cover M| = #|M| * 4.
Proof.
move=> matM; have [_ /eqP <-] := matchingP matM; rewrite -sum_nat_const.
by apply: eq_bigr => S SM; rewrite (card_square (matching_sub matM SM)).
Qed.

End Squares.

Arguments faceP {m x F y}.
