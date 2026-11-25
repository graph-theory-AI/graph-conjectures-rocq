(** * R_l(H_s, k) = s^k + 1

Upper bound, with the same list of k colours on all edges: if all colour classes are
s-colourable, the product of their colourings is an injection into [s]^k, so that there are at
most s^k vertices.

Lower bound, for lists L on the edges of K_n with n <= s^k: give to the vertices, one after the
other, labels in [s]^C, where C is the set of all colours, such that the labels of x and y
differ in some colour of L(xy).  This is possible: for each of the less than s^k previous
vertices x, a proportion s^-k of the labels agree with that of x in all colours of L(xy).  Then
give to xy a colour of L(xy) where the labels of x and y differ: for each colour c, the c-th
coordinate of the labels is a proper s-colouring of the class of c.

The proof comes from Graph-Theory-LLM-Proofs (attacks/2103.15175__00).  It was formalized in
graph-theory-rocq (extremal-graph-theory/theories/applications/list_ramsey_graph). *)

From GraphTheory Require Import digraph sgraph coloring.
From GC.GraphLib Require Import chromatic.
From GC.extremal.AX_list_ramsey_chromatic_family_exact Require main.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Abbreviation edge_color_class := main.edge_color_class.
Abbreviation list_ramsey_chromatic_arrows := main.list_ramsey_chromatic_arrows.

(** The [s]-colourability of a colour class. *)
Lemma class_colorable (G : sgraph) (C : eqType) (col : {set G} -> C) (c : C) (s : nat) :
  χ([set: edge_color_class col (pred1 c)]) <= s <->
  exists g : G -> 'I_s, forall x y : G, x -- y -> col [set x; y] = c -> g x != g y.
Proof.
have adj (x y : G) : @edge_rel (edge_color_class col (pred1 c)) x y =
    (x -- y) && (col [set x; y] == c).
  by rewrite /edge_rel /= /main.del_edge_set_rel /= inE negbK.
split=> [/chi_leP[g /proper_coloringP pg]|[g pg]].
- by exists g => x y xy /eqP col_xy; apply: pg; rewrite adj xy.
- apply/chi_leP; exists g; apply/proper_coloringP => x y.
  by rewrite adj => /andP[xy /eqP]; exact: pg.
Qed.

(** ** The upper bound *)

(** The same list on all edges. *)
Lemma common_lists_arrow (s k : nat) : list_ramsey_chromatic_arrows 'K_(s ^ k).+1 k s.
Proof.
exists 'I_k, (fun _ => setT); split=> [_|col _]; first by rewrite cardsT card_ord.
apply/existsP; apply: contraT; rewrite negb_exists => /forallP small.
have /fin_all_exists[g pg] (c : 'I_k) := (class_colorable col c s).1 (contraNleq id (small c)).
have /leq_card : injective (fun x => [ffun c => g c x]).
  move=> x y eq_xy; apply: contraTeq (eqxx (g (col [set x; y]) x)) => /pg/(_ erefl).
  by move/ffunP/(_ (col [set x; y])): eq_xy; rewrite !ffunE => {1}<-.
by rewrite card_ffun !card_ord ltnn.
Qed.

(** ** The lower bound *)

Section LowerBound.
Variables (n s k : nat) (C : finType) (L : {set 'K_n} -> {set C}).
Hypotheses (s_gt0 : 0 < s) (k_gt0 : 0 < k) (Lk : forall e, #|L e| = k).

Abbreviation label := {ffun C -> 'I_s}.

(** The labels that agree with [a] on [S]. *)
Definition subcube (S : {set C}) (a : label) : {set label} :=
  [set b : label | [forall c in S, b c == a c]].

Lemma card_subcube (S : {set C}) (a : label) : #|subcube S a| * s ^ #|S| = s ^ #|C|.
Proof.
pose F c := [pred y | (c \in S) ==> (y == a c)].
have -> : #|subcube S a| = #|family F| by apply: eq_card => b; rewrite inE.
rewrite card_family foldrE big_map big_enum -!prod_nat_const [in LHS](big_mkcond [in S]) /=.
rewrite -big_split /=; apply: eq_bigr => c _; case: (c \in S); last by rewrite muln1 card_ord.
by rewrite (card1 (a c)) mul1n.
Qed.

(** A label for [x], given the labels [f v] of less than [s ^ k] vertices [v]. *)
Lemma next_label (f : 'K_n -> label) (x : 'K_n) (A : {set 'K_n}) :
  #|A| < s ^ k ->
  exists b : label, forall v, v \in A -> exists2 c, c \in L [set x; v] & b c != f v c.
Proof.
move=> ltA; pose P := [set subcube (L [set x; v]) (f v) | v in A].
have le_cover : #|cover P| * s ^ k <= #|A| * s ^ #|C|.
  apply: (@leq_trans (#|P| * s ^ #|C|)); last by rewrite leq_mul2r leq_imset_card orbT.
  apply: leq_trans (leq_mul (leq_card_cover P) (leqnn _)) _.
  rewrite -sum_nat_const big_distrl /= leq_sum //.
  by move=> _ /imsetP[v _ ->]; rewrite -(Lk [set x; v]) card_subcube.
have /subsetPn[b _ bP] : ~~ ([set: label] \subset cover P).
  apply: contraTN ltA => /subset_leq_card; rewrite cardsT card_ffun card_ord -leqNgt => le_s.
  rewrite -(leq_pmul2r (_ : 0 < s ^ #|C|)) ?expn_gt0 ?s_gt0 // mulnC.
  by rewrite (leq_trans _ le_cover) // leq_mul2r le_s orbT.
exists b => v vA; have : b \notin subcube (L [set x; v]) (f v).
  apply: contra bP => bv; apply/bigcupP; exists (subcube (L [set x; v]) (f v)) => //.
  exact: imset_f.
by rewrite inE negb_forall_in => /exists_inP.
Qed.

(** Labels such that, for any two vertices, they differ in some colour of the list of the edge. *)
Lemma separating_labels (vs : seq 'K_n) :
  size vs <= s ^ k ->
  exists f : 'K_n -> label, forall x y, x \in vs -> y \in vs -> x != y ->
    exists2 c, c \in L [set x; y] & f x c != f y c.
Proof.
elim: vs => [_|x vs IH lt_vs]; first by exists (fun _ => [ffun=> Ordinal s_gt0]).
have [f sep_f] := IH (ltnW lt_vs).
have [|b sep_b] := @next_label f x [set v in vs].
  by rewrite cardsE (leq_ltn_trans (card_size _)).
exists (fun v => if v == x then b else f v) => u v; rewrite !inE.
have [-> _|ux /= uvs] := eqVneq u x; have [->|vx /= vvs] := eqVneq v x; rewrite ?eqxx //.
- by move=> _; apply: sep_b; rewrite inE.
- by case: (sep_b u) => [|c]; rewrite ?inE // setUC eq_sym; exists c.
- exact: sep_f.
Qed.

(** From any lists, the edges can be coloured such that all classes are [s]-colourable. *)
Lemma lists_avoid :
  n <= s ^ k ->
  exists2 col : {set 'K_n} -> C, forall e, col e \in L e &
    forall c, χ([set: edge_color_class col (pred1 c)]) <= s.
Proof.
move=> le_n; have [|f sep_f] := @separating_labels (enum 'K_n); first by rewrite -cardE card_ord.
pose separates (e : {set 'K_n}) c := 1 < #|[set f x c | x in e]|.
have separates2 x y c : separates [set x; y] c = (f x c != f y c).
  by rewrite /separates imsetU1 imset_set1 cards2 ltnS lt0b.
have /fin_all_exists2[col colL col_sep] (e : {set 'K_n}) :
    exists2 c, c \in L e & [exists c' in L e, separates e c'] -> separates e c.
  have [/exists_inP[c]|_] := boolP [exists c in L e, separates e c]; first by exists c.
  have /card_gt0P[c cL] : 0 < #|L e| by rewrite Lk.
  by exists c.
exists col => // c; apply/class_colorable; exists (fun x => f x c) => x y xy <-.
rewrite -separates2 col_sep //; have [||c' c'L sep] := sep_f x y _ _ xy; rewrite ?mem_enum //.
by apply/exists_inP; exists c'; rewrite ?separates2.
Qed.

End LowerBound.

Theorem list_ramsey_chromatic_family : main.AX_list_ramsey_chromatic_family_exact.
Proof.
move=> s k /ltnW s_gt0 k_gt0; split=> [|n [C [L [Lk arrow]]]]; first exact: common_lists_arrow.
rewrite ltnNge; apply/negP => le_n.
have [col colL small] := lists_avoid s_gt0 k_gt0 Lk le_n.
by have [c] := arrow col colL; rewrite ltnNge small.
Qed.
