(** * The Erdős-Hajnal conjecture implies its version for graphs of bounded VC-dimension

Let H_n be the bipartite graph whose vertices are the elements and the subsets of {1, ..., n}, an
element being adjacent to the subsets that contain it.  The elements form a shattered set, so H_n
has VC-dimension at least n.  As the VC-dimension does not increase on induced subgraphs, a graph
of VC-dimension at most d has no induced copy of H_(d+1), and the Erdős-Hajnal conjecture for
H_(d+1) gives the conclusion.

The implication is the edge e116 of relations.json in graph-conjectures.  It was formalized in
graph-theory-rocq (extremal-graph-theory/theories/conjectures/implications_X223.v). *)

From GraphTheory Require Import digraph sgraph dom coloring.
From mathcomp Require Import boot.
From GC.GraphLib Require extremal.
From GC.extremal.OPG_erdos_hajnal_induced_cliques Require Import
  main(OPG_erdos_hajnal_induced_cliques).
From GC.extremal.AX_bounded_vc_dimension_erdos_hajnal Require Import
  main(AX_bounded_vc_dimension_erdos_hajnal).

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Abbreviation shattered := GC.extremal.AX_bounded_vc_dimension_erdos_hajnal.main.shattered.
Abbreviation vc_dim_le := GC.extremal.AX_bounded_vc_dimension_erdos_hajnal.main.vc_dim_le.

(** ** A graph of VC-dimension at least [n] *)

Section ShatterGraph.
Variable n : nat.

(** The elements of ['I_n] are adjacent to the subsets that contain them. *)
Definition shatter_rel : rel ('I_n + {set 'I_n}) := fun x y =>
  match x, y with inl i, inr A | inr A, inl i => i \in A | _, _ => false end.

Lemma shatter_sym : symmetric shatter_rel. Proof. by case=> ? []. Qed.
Lemma shatter_irrefl : irreflexive shatter_rel. Proof. by case. Qed.

Definition shatter_graph : sgraph := SGraph shatter_sym shatter_irrefl.

End ShatterGraph.

(** The elements form a shattered set. *)
Lemma shatter_graph_vc (d : nat) : ~ vc_dim_le (shatter_graph d.+1) d.
Proof.
pose L : {set shatter_graph d.+1} := inl @: [set: 'I_d.+1].
have shL : shattered L.
  move=> T /subsetP TL; exists (inr [set i | inl i \in T]); apply/setP => -[i|A].
    by rewrite !inE (_ : _ -- _ = (i \in [set i | inl i \in T])) // inE imset_f ?andbT.
  have AL : inr A \notin L by apply/imsetP => -[].
  by rewrite inE (negbTE AL) andbF; apply/esym/negP => /TL; apply/negP.
move/(_ L shL); rewrite card_imset ?cardsT ?card_ord ?ltnn //; exact: inl_inj.
Qed.

(** ** The implication *)

Theorem OPG_erdos_hajnal_induced_cliques_implies_AX_bounded_vc_dimension_erdos_hajnal :
  OPG_erdos_hajnal_induced_cliques -> AX_bounded_vc_dimension_erdos_hajnal.
Proof.
move=> EH d _; have [a [b [a0 [ab EHd]]]] := EH (shatter_graph d.+1).
exists b; split=> [|G vc]; first exact: leq_trans a0 ab.
have [S clS MS] : exists2 S : {set G},
    cliqueb S || stable S & maxn ω([set: G]) α([set: G]) <= #|S|.
  case: omegaP => K; rewrite !inE -andbA => /and3P[_ clK _].
  case: alphaP => T; rewrite !inE -andbA => /and3P[_ stT _].
  by case: leqP; [exists T | exists K]; rewrite ?stT ?clK ?orbT.
exists S; split=> //; have [->//|G0] := posnP #|G|.
have free : ~ inhabited (shatter_graph d.+1 ⇀ G).
  by case=> i; apply: (@shatter_graph_vc d); apply: extremal.vc_dim_le_isubgraph i _ vc.
apply: leq_trans (leq_trans (EHd G G0 free) _); first by rewrite -{1}(expn1 #|G|) leq_pexp2l.
by rewrite leq_exp2r // (leq_trans a0 ab).
Qed.

Check (OPG_erdos_hajnal_induced_cliques_implies_AX_bounded_vc_dimension_erdos_hajnal :
  GC.extremal.OPG_erdos_hajnal_induced_cliques.main.OPG_erdos_hajnal_induced_cliques ->
  GC.extremal.AX_bounded_vc_dimension_erdos_hajnal.main.AX_bounded_vc_dimension_erdos_hajnal).
Print Assumptions
  OPG_erdos_hajnal_induced_cliques_implies_AX_bounded_vc_dimension_erdos_hajnal.
