(** * The triangle has no Alon-Tarsi orientation with the required outdegrees

    Let A be the arc set of an orientation of a spanning subgraph of the triangle where each vertex
    has outdegree at least (2 - 1) / 2.  Each outdegree is at least 1, hence each indegree is at
    most 1, since a vertex has only two neighbours.  The outdegrees and the indegrees have the same
    sum, thus all of them are 1: A is a directed triangle.  (If the bound were rounded down to an
    integer, the empty arc set would do.)

    An Eulerian arc set A with an odd number of arcs is not an Alon-Tarsi orientation: B |-> A \ B
    is a bijection between its Eulerian subsets with an even number of arcs and those with an odd
    number of arcs.

    The proof comes from Graph-Theory-LLM-Proofs (attacks/2209.09107__00).  It was formalized in
    graph-theory-rocq (chromatic-theory/theories/applications/alon_tarsi_triangle.v). *)

From GraphTheory Require Import digraph sgraph.
From mathcomp Require Import boot.
From GC.GraphLib Require Import digraph chromatic(eulerian_subsets, alon_tarsi).
From GC.chromatic.AX_alon_tarsi_orientation_half_out_degree Require main.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Eulerian arc sets with an odd number of arcs *)

Section Eulerian.
Variable (V : finType).
Implicit Types (A B : {set V * V}) (v : V).

(** Degrees in a difference of arc sets. *)
Lemma card_preimsetD (T : finType) (f : T -> V * V) A B : B \subset A ->
  #|f @^-1: A| = #|f @^-1: B| + #|f @^-1: (A :\: B)|.
Proof. by move=> BA; rewrite -(cardsID (f @^-1: B)) -preimsetI -preimsetD (setIidPr BA). Qed.

Lemma outdeg_setD A B v : B \subset A ->
  outdeg (D := digraph_of_arcs A) v =
  outdeg (D := digraph_of_arcs B) v + outdeg (D := digraph_of_arcs (A :\: B)) v.
Proof. exact: card_preimsetD (pair v) _ _. Qed.

Lemma indeg_setD A B v : B \subset A ->
  indeg (D := digraph_of_arcs A) v =
  indeg (D := digraph_of_arcs B) v + indeg (D := digraph_of_arcs (A :\: B)) v.
Proof. exact: card_preimsetD (fun u => (u, v)) _ _. Qed.

(** A subset of an Eulerian arc set is Eulerian iff its complement is. *)
Lemma balanced_setD A B : B \subset A -> balanced_digraph (digraph_of_arcs A) ->
  balanced_digraph (digraph_of_arcs (A :\: B)) = balanced_digraph (digraph_of_arcs B).
Proof.
move=> BA /forallP balA; apply: eq_forallb => v; move: (balA v).
rewrite (indeg_setD v BA) (outdeg_setD v BA) => /eqP eq_deg.
by rewrite -(eqn_add2l (indeg (D := digraph_of_arcs B) v)) eq_deg eqn_add2r eq_sym.
Qed.

Lemma odd_eulerian_not_alon_tarsi A :
  balanced_digraph (digraph_of_arcs A) -> odd #|A| -> ~~ alon_tarsi A.
Proof.
move=> balA oddA; rewrite negbK -!sum1_card; apply/eqP.
rewrite (reindex_onto (setD A) (setD A)) => [B|].
  by rewrite !inE setDDr setDv set0U => /andP[/andP[BA _] _]; apply/setIidPr.
apply: eq_bigl => B; rewrite !inE subsetDl setDDr setDv set0U -(sameP setIidPr eqP).
case BA: (B \subset A); rewrite ?andbF //= andbT balanced_setD // cardsDS //.
by rewrite oddB ?subset_leq_card // oddA negbK.
Qed.

End Eulerian.

(** ** The triangle *)

Theorem triangle : ~ main.AX_alon_tarsi_orientation_half_out_degree.
Proof.
move=> /(_ 'K_3)[A [orA atA degA]]; pose D := digraph_of_arcs A.
have out_gt0 (v : D) : 0 < outdeg v.
  have: 1 < (2 * outdeg v).+1 := leq_trans (deg_Kn (v : 'K_3)) (degA v).
  by case: (outdeg v).
have in_le1 (v : D) : indeg v <= 1.
  have /card_gt0P[w] := out_gt0 v; rewrite inE => vw.
  have [vNw wNv] : v != w /\ (w, v) \notin A := orA _ _ vw.
  have sub : [set u : D | u -- v] \subset ~: [set v; w].
    apply/subsetP => u; rewrite !inE => uv; have [uNv _] : u != v /\ _ := orA _ _ uv.
    by rewrite negb_or uNv; apply: contraNneq wNv => <-.
  by apply: leq_trans (subset_leq_card sub) _; rewrite cardsCs setCK cards2 vNw card_ord.
have bal : balanced_digraph D.
  have [_] := leqif_sum (fun v (_ : xpredT v) => leqif_eq (leq_trans (in_le1 v) (out_gt0 v))).
  by rewrite sum_indeg sum_outdeg eqxx.
move: atA; apply/negP/(odd_eulerian_not_alon_tarsi bal).
rewrite -num_edges_digraph_of_arcs -sum_outdeg (eq_bigr (fun=> 1)) => [v _|].
  by apply/eqP; rewrite eqn_leq out_gt0 -(eqP (forallP bal v)) in_le1.
by rewrite sum1_card card_ord.
Qed.
