(** * Meyniel's conjecture for k-uniform hypergraphs implies Meyniel's conjecture

Let G be a connected graph on n vertices.  If n >= 2, its edges form a connected 2-uniform
hypergraph whose 2-section is G, so that its cop number c satisfies 2 c^2 <= C^2 n, hence
c <= C ⌈√n⌉.  If n = 1, the hypergraph with the single edge V(G) is connected and 1-uniform, and
its 2-section is G again.  The constant C is the same.

The implication is the edge e243 of relations.json in graph-conjectures.  It was formalized in
graph-theory-rocq (atlas/theories/conjectures/implications_A1.v). *)

From GraphTheory Require Import preliminaries digraph sgraph.
From mathcomp Require Import boot.
From GC.hypergraph.AX_meyniel_cop_number_k_uniform_hypergraph Require Import
  main(AX_meyniel_cop_number_k_uniform_hypergraph).
From GC.misc.OTH_meyniel_cop_number_sqrt_n Require Import main(OTH_meyniel_cop_number_sqrt_n).

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Abbreviation two_section :=
  GC.hypergraph.AX_meyniel_cop_number_k_uniform_hypergraph.main.two_section.
Abbreviation hg_uniform :=
  GC.hypergraph.AX_meyniel_cop_number_k_uniform_hypergraph.main.hg_uniform.
Abbreviation hg_connected :=
  GC.hypergraph.AX_meyniel_cop_number_k_uniform_hypergraph.main.hg_connected.
Abbreviation hg_adjacent :=
  GC.hypergraph.AX_meyniel_cop_number_k_uniform_hypergraph.main.hg_adjacent.
Abbreviation sqrt_ceil := GC.misc.OTH_meyniel_cop_number_sqrt_n.main.sqrt_ceil.

Section SameEdges.
Variables (G : sgraph) (E : {set {set G}}).
Hypothesis sameE : forall x y : G, @edge_rel (two_section E) x y = x -- y.

(** The game on the 2-section of [E] is the game on [G]. *)
Lemma cops_capture_two_section k t (C : {ffun 'I_k -> G}) r :
  GC.hypergraph.AX_meyniel_cop_number_k_uniform_hypergraph.main.cops_capture
    (G := two_section E) t C r =
  GC.misc.OTH_meyniel_cop_number_sqrt_n.main.cops_capture (G := G) t C r.
Proof.
elim: t C r => [//|t IH] C r; rewrite /=; congr (_ || _); apply: eq_existsb => C'.
congr (_ && (_ || _)); first by apply: eq_forallb => i; rewrite /dominates sameE.
by apply: eq_forallb => r'; rewrite /dominates sameE IH.
Qed.

End SameEdges.

Theorem AX_meyniel_cop_number_k_uniform_hypergraph_implies_OTH_meyniel_cop_number_sqrt_n :
  AX_meyniel_cop_number_k_uniform_hypergraph -> OTH_meyniel_cop_number_sqrt_n.
Proof.
case=> C hC; exists C => G G0 conG.
suff [E [k [k0 kG uE cE sameE]]] : exists (E : {set {set G}}) k,
    [/\ 0 < k, k <= #|G|, hg_uniform E k, hg_connected E &
        forall x y : G, @edge_rel (two_section E) x y = x -- y].
  have [c [[t win] le]] := hC G E k k0 kG uE cE; exists c; split; last first.
    exists t; apply: etrans _ win; apply: eq_existsb => C0; apply: eq_forallb => r0.
    exact/esym/cops_capture_two_section.
  rewrite -(@leq_exp2r _ _ 2) // expnMn (leq_trans (leq_pmulr _ k0) (leq_trans le _)) //.
  by rewrite leq_mul2l /sqrt_ceil; case: ex_minnP => s ->; rewrite orbT.
case: (ltnP 1 #|G|) => G1.
- exists E(G), 2; split => //.
  + by move=> e /edgesP[x [y [-> xy]]]; rewrite cards2 (sg_edgeNeq xy).
  + move=> u v; apply: connect_sub (connectedTE conG u v) => x y xy; apply: connect1.
    by apply/existsP; exists [set x; y]; rewrite in_edges xy !inE !eqxx orbT.
  move=> x y; case: (eqVneq x y) => [<-|xy]; first by rewrite !sg_irrefl.
  rewrite /edge_rel /= xy /sc /=.
  have adj a b : hg_adjacent E(G) a b -> a != b -> a -- b.
    move=> /existsP[e /and3P[/edgesP[u [v [-> uv]]]]].
    by rewrite !inE => /pred2P[] -> /pred2P[] ->; rewrite ?eqxx // sgP.
  apply/orP/idP => [[] /adj|xy']; [exact | rewrite sgP eq_sym; exact | left].
  by apply/existsP; exists [set x; y]; rewrite in_edges !inE !eqxx /= orbT andbT.
- have one (x y : G) : x = y by apply: (card_le1_eqP G1).
  exists [set setT], 1; split => //.
  + by move=> e; rewrite inE => /eqP ->; rewrite cardsT; apply/eqP; rewrite eqn_leq G1.
  + by move=> u v; rewrite (one u v) connect0.
  by move=> x y; rewrite (one x y) !sg_irrefl.
Qed.

Check (AX_meyniel_cop_number_k_uniform_hypergraph_implies_OTH_meyniel_cop_number_sqrt_n :
  GC.hypergraph.AX_meyniel_cop_number_k_uniform_hypergraph.main.AX_meyniel_cop_number_k_uniform_hypergraph ->
  GC.misc.OTH_meyniel_cop_number_sqrt_n.main.OTH_meyniel_cop_number_sqrt_n).
Print Assumptions AX_meyniel_cop_number_k_uniform_hypergraph_implies_OTH_meyniel_cop_number_sqrt_n.
