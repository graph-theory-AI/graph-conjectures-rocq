(** * The counterexample: a planar graph with 12 vertices and feedback vertex number 5

The graph consists of a 4-cycle [a b c d] and of two cliques [p0 q0 r0 s0] and [p1 q1 r1 s1],
where [p0], [q0] are attached to [b], [d], and [p1], [q1] to [a], [c]. *)

From GraphTheory Require Import digraph sgraph.
From mathcomp Require Import boot.
From GC.GraphLib Require Import misc.
From GC.misc.AX_planar_fvs_face_packing_ratio_2 Require main.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Abbreviation feedback_vertex_set := main.feedback_vertex_set.
Abbreviation feedback_vertex_number := main.feedback_vertex_number.

(** ** The graph *)

(** The vertices: the 4-cycle [a b c d] and two cliques [p q r s]. *)
Definition a : 'I_12 := @Ordinal 12 0 isT.
Definition b : 'I_12 := @Ordinal 12 1 isT.
Definition c : 'I_12 := @Ordinal 12 2 isT.
Definition d : 'I_12 := @Ordinal 12 3 isT.
Definition p0 : 'I_12 := @Ordinal 12 4 isT.
Definition q0 : 'I_12 := @Ordinal 12 5 isT.
Definition r0 : 'I_12 := @Ordinal 12 6 isT.
Definition s0 : 'I_12 := @Ordinal 12 7 isT.
Definition p1 : 'I_12 := @Ordinal 12 8 isT.
Definition q1 : 'I_12 := @Ordinal 12 9 isT.
Definition r1 : 'I_12 := @Ordinal 12 10 isT.
Definition s1 : 'I_12 := @Ordinal 12 11 isT.

Definition vertices : seq 'I_12 := [:: a; b; c; d; p0; q0; r0; s0; p1; q1; r1; s1].

(** The neighbours of [v], in the cyclic order given by an embedding in the plane. *)
Definition nb (v : 'I_12) : seq 'I_12 :=
  nth [::] [:: [:: b; d; p1]; [:: a; c; p0]; [:: b; q1; d]; [:: c; a; q0];
               [:: q0; r0; s0; b]; [:: p0; d; s0; r0]; [:: p0; q0; s0]; [:: p0; r0; q0];
               [:: q1; r1; s1; a]; [:: p1; c; s1; r1]; [:: p1; q1; s1]; [:: p1; r1; q1]] v.

Lemma mem_vertices v : v \in vertices.
Proof. by case: v => [[|[|[|[|[|[|[|[|[|[|[|[|]]]]]]]]]]]]]. Qed.

Lemma all_vertices (P : pred 'I_12) : all P vertices -> forall v, P v.
Proof. by move=> /allP H v; exact: H (mem_vertices v). Qed.

Definition adj : rel 'I_12 := fun u v => v \in nb u.

Lemma adj_sym : symmetric adj.
Proof.
move=> u v; apply/eqP; apply: (all_vertices (P := fun v => adj u v == adj v u)).
by apply: (all_vertices (P := fun u => all (fun v => adj u v == adj v u) vertices)); vm_compute.
Qed.

Lemma adj_irrefl : irreflexive adj.
Proof. by move=> v; apply/negbTE; apply: (all_vertices (P := fun v => ~~ adj v v)); vm_compute. Qed.

Definition G12 : sgraph := SGraph adj_sym adj_irrefl.

Lemma nbP (u v : G12) : (v \in nb u) = (u -- v).
Proof. by []. Qed.

Lemma nbU (v : G12) : uniq (nb v).
Proof. by apply: (all_vertices (P := fun v => uniq (nb v))); vm_compute. Qed.

Lemma opn_nb (v : G12) : N(v) = [set:: nb v].
Proof. by apply/setP => u; rewrite !inE. Qed.

Lemma degree (v : G12) : #|N(v)| = size (nb v).
Proof. by rewrite opn_nb cardsE (card_uniqP (nbU v)). Qed.

Lemma card_edges : #|E(G12)| = 20.
Proof.
apply: double_inj; rewrite -mul2n edges_sum_degrees.
by under eq_bigr do rewrite degree; rewrite !big_ord_recl big_ord0.
Qed.

(** A cycle contains at least two neighbours of each of its vertices. *)
Lemma cycle_nb (s : seq G12) v : seq_cycle (--) s -> v \in s -> 1 < count (mem s) (nb v).
Proof.
move=> cs vs; have := seq_cycle_degree cs vs; rewrite opn_nb -size_filter.
rewrite -(card_uniqP (filter_uniq _ (nbU v))); congr (_ < _); apply: eq_card => u.
by rewrite inE mem_filter !inE andbC.
Qed.

(** Each vertex but [a] has a neighbour before it. *)
Lemma connected_G12 : connected [set: G12].
Proof.
have ca (v : G12) : connect (--) (a : G12) v.
  have [n] := ubnP (v : nat); elim: n v => // n IH v lt_vn.
  have : (v == a) || has (fun u : G12 => u < v) (nb v).
    by apply: (all_vertices (P := fun v => (v == a) || has (fun u : 'I_12 => u < v) (nb v))).
  case/orP => [/eqP->|/hasP[u uv lt_uv]]; first exact: connect0.
  apply: connect_trans (IH u (leq_trans lt_uv lt_vn)) (connect1 _).
  by rewrite sg_sym -nbP.
apply: connectedTI => u v; apply: connect_trans (ca v).
by rewrite sym_connect_sym //; exact: sg_sym.
Qed.

(** ** The 4-cycle and the cliques *)

(** 0 for the vertices of the 4-cycle, 1 and 2 for those of the cliques. *)
Definition part (v : 'I_12) : nat := v %/ 4.

(** The pairs of adjacent vertices. *)
Definition edges : seq (G12 * G12) := [seq (u, v) | u <- vertices, v <- nb u].

Lemma all_edges (P : pred (G12 * G12)) : all P edges -> forall u v, u -- v -> P (u, v).
Proof.
move=> /allP H u v uv; apply: H; apply/allpairsPdep; exists u, v.
by rewrite mem_vertices nbP.
Qed.

(** A vertex of the 4-cycle has two neighbours in it. *)
Lemma part_cycle (u : G12) :
  part u = 0 -> size (nb u) = 3 /\ count (fun v => part v == 0) (nb u) = 2.
Proof.
move=> /eqP; have /implyP H := all_vertices (P := fun u => (part u == 0) ==>
  (size (nb u) == 3) && (count (fun v => part v == 0) (nb u) == 2)) isT u.
by case/H/andP => /eqP-> /eqP->.
Qed.

(** A clique is only adjacent to the 4-cycle. *)
Lemma part_exit (u v : G12) : u -- v -> part u != 0 -> part v != part u -> part v = 0.
Proof.
move=> uv; have := all_edges
  (P := fun e => [|| part e.1 == 0, part e.2 == part e.1 | part e.2 == 0]) isT uv.
by case/or3P => /= /eqP-> //; rewrite ?eqxx.
Qed.

(** A vertex of a clique has at most one neighbour on the 4-cycle. *)
Lemma part_clique (u v w : G12) :
  u -- v -> u -- w -> part u != 0 -> part v = 0 -> part w = 0 -> v = w.
Proof.
move=> uv uw pu /eqP pv /eqP pw.
have := all_edges (P := fun e => [|| part e.1 == 0, part e.2 != 0 |
  all (fun w => (part w != 0) || (e.2 == w)) (nb e.1)]) isT uv.
by rewrite /= pv (negbTE pu) => /allP/(_ w uw); rewrite pw => /eqP.
Qed.

(** The cliques adjacent to consecutive vertices of the 4-cycle are distinct. *)
Lemma part_alt (u v u' v' : G12) : u -- u' -> u -- v -> u' -- v' ->
  part u = 0 -> part u' = 0 -> part v != 0 -> part v' != 0 -> part v' = 3 - part v.
Proof.
move=> uu' uv uv' /eqP pu /eqP pu' pv pv'.
have := all_edges (P := fun e => [&& part e.1 == 0 & part e.2 == 0] ==>
  all (fun v => all (fun v' => [|| part v == 0, part v' == 0 | part v' == 3 - part v])
    (nb e.2)) (nb e.1)) isT uu'.
rewrite /= pu pu' /= => /allP/(_ v uv)/allP/(_ v' uv').
by rewrite (negbTE pv) (negbTE pv') => /eqP.
Qed.

Lemma part_lt3 (v : G12) : part v < 3.
Proof. exact: (all_vertices (P := fun v => part v < 3)). Qed.

Lemma min_degree_G12 : min_degree_ge G12 2.
Proof. by move=> v; rewrite degree; apply: (all_vertices (P := fun v => 1 < size (nb v))). Qed.

(** ** The feedback vertex number is 5 *)

(** A set that meets the triangles of a clique on four vertices has at least two of them. *)
Lemma feedback_K4 (X : pred G12) (p q r s : G12) :
  all (has X) [:: [:: p; q; r]; [:: p; q; s]; [:: p; r; s]; [:: q; r; s]] ->
  1 < count X [:: p; q; r; s].
Proof. by move=> /=; case: (X p); case: (X q); case: (X r); case: (X s). Qed.

(** A feedback vertex set has a vertex of the 4-cycle and two vertices of each clique. *)
Lemma feedback_lower (X : {set G12}) : feedback_vertex_set X -> 5 <= #|X|.
Proof.
move=> fX; have hit (s : seq G12) : seq_cycle (--) s -> has (mem X) s.
  by move=> /fX[v vs vX]; apply/hasP; exists v.
have -> : #|X| = count (mem X) vertices.
  rewrite -size_filter -(card_uniqP (filter_uniq _ (isT : uniq vertices))).
  by apply: eq_card => v; rewrite mem_filter mem_vertices andbT.
rewrite -[vertices]/([:: a; b; c; d] ++ [:: p0; q0; r0; s0] ++ [:: p1; q1; r1; s1]) !count_cat.
apply: (@leq_add 1 4); first by rewrite -has_count; exact: hit.
by apply: (@leq_add 2 2); apply: feedback_K4; apply/allP => t;
  rewrite !inE => /or4P[] /eqP->; exact: hit.
Qed.

(** If the cycle [s] avoids [R], it avoids the vertices with at most one neighbour outside [R]. *)
Lemma avoid_cons (s R : seq G12) v :
  seq_cycle (--) s -> {in R, forall u, u \notin s} -> count (fun u => u \notin R) (nb v) <= 1 ->
  {in v :: R, forall u, u \notin s}.
Proof.
move=> cs avoid le1 u; rewrite inE => /predU1P[->|/avoid//].
apply/negP => /(cycle_nb cs); rewrite ltnNge => /negP[]; apply: leq_trans le1.
by apply: sub_count => w; apply: contraTN => /avoid.
Qed.

(** This set meets all cycles: the other vertices induce a forest. *)
Definition hitting : seq G12 := [:: a; p0; q0; p1; q1].

Lemma feedback_upper : feedback_vertex_set [set:: hitting].
Proof.
move=> s cs; have [/hasP[v vs vS]|/hasPn out] := boolP (has (mem hitting) s).
  by exists v => //; rewrite inE.
have avoid : {in [:: c; d; b; s1; r1; s0; r0] ++ hitting, forall u, u \notin s}.
  by do 7!apply: avoid_cons => //; move=> u uS; by apply: contraTN uS => /out.
case: s cs out avoid => // v s _ _ /(_ v); rewrite mem_head; case/(_ _)/negP => //.
exact: (all_vertices (P := mem ([:: c; d; b; s1; r1; s0; r0] ++ hitting))).
Qed.

Lemma feedback_number_G12 : feedback_vertex_number G12 5.
Proof.
split; last exact: feedback_lower.
by exists [set:: hitting]; split; [exact: feedback_upper | rewrite cardsE (card_uniqP _)].
Qed.
